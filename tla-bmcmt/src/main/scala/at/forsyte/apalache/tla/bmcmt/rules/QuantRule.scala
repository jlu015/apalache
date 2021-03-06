package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, PowSetT}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import com.typesafe.scalalogging.LazyLogging

/**
  * Implements the rules: SE-LOG-EX[1-3] and SE-LOG-ALL[1-3].
  *
  * @author Igor Konnov
  */
class QuantRule(rewriter: SymbStateRewriter) extends RewritingRule with LazyLogging {
  private val pickRule = new PickFromAndFunMerge(rewriter, failWhenEmpty = false)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.exists, _, _, _) => true
      case OperEx(TlaBoolOper.forall, _, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaBoolOper.exists, NameEx(boundVar), boundingSetEx, predEx) =>
        if (rewriter.freeExistentialsStore.isFreeExists(state.ex.ID)) {
          val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(boundingSetEx))
          val set = setState.arena.findCellByNameEx(setState.ex)
          val finalState = set.cellType match {
            case FinSetT(_) =>
              freeExistsInSet(setState, boundVar, predEx, set)

            case PowSetT(FinSetT(_)) => ()
              // TODO: include in the report
              freeExistsInPowerset(setState, boundVar, predEx, set)

            case tp =>
              throw new UnsupportedOperationException("Quantification over %s is not supported yet".format(tp))
          }
          rewriter.coerce(finalState, state.theory)
        } else {
          expandExistsOrForall(isExists = true, state, boundVar, boundingSetEx, predEx)
        }

      case OperEx(TlaBoolOper.forall, NameEx(boundVar), boundingSetEx, predEx) =>
        expandExistsOrForall(isExists = false, state, boundVar, boundingSetEx, predEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def expandExistsOrForall(isExists: Boolean,
                                    state: SymbState, boundVar: String, boundingSetEx: TlaEx, predEx: TlaEx) = {
    rewriter.solverContext.log("; quanitification over a finite set => expanding")
    // first, evaluate boundingSet
    val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(boundingSetEx))
    val set = setState.arena.findCellByNameEx(setState.ex)
    set.cellType match {
      case PowSetT(_) =>
        logger.warn("Unfolding a subset is inefficient. Consider using a free-standing quantifier \\E X \\in SUBSET {...}: P")
        throw new UnsupportedOperationException("A quantified expression was about to unfold %s".format(setState.ex))

      case FinSetT(_) => () // supported

      case tp =>
        throw new UnsupportedOperationException("Quantification over %s is not supported yet".format(tp))
    }
    val setCells = setState.arena.getHas(set)  // <------- THIS IS A BUG that does not work with SUBSET!
    val finalState =
      if (setCells.isEmpty) {
        // 'exists' over an empty set always returns false, while 'forall' returns true
        val constResult =
          if (isExists)
            rewriter.solverContext.falseConst
          else
            rewriter.solverContext.trueConst

        setState.setTheory(BoolTheory()).setRex(NameEx(constResult))
      } else {
        def mkPair(elemCell: ArenaCell): (Binding, TlaEx) = {
          val newBinding = setState.binding + (boundVar -> elemCell)
          (newBinding, predEx)
        }

        // rewrite p[c_i/x] for every c_i \in boundingSet
        val (predState: SymbState, predEs: Seq[TlaEx]) =
          rewriter.rewriteBoundSeqUntilDone(setState.setTheory(BoolTheory()), setCells.map(mkPair))

        val nonEmpty = tla.or(setCells.map(tla.in(_, set)): _*)
        val empty = tla.and(setCells.map(c => tla.not(tla.in(c, set))): _*)

        def elemWitnesses(elemAndPred: (ArenaCell, TlaEx)): TlaEx = {
          tla.and(tla.in(elemAndPred._1, set), elemAndPred._2)
        }

        def elemSatisfies(elemAndPred: (ArenaCell, TlaEx)): TlaEx = {
          tla.or(tla.not(tla.in(elemAndPred._1, set)), elemAndPred._2)
        }

        val pred = NameEx(rewriter.solverContext.introBoolConst())
        val iff =
          if (isExists) {
            // \E x \in S: p holds iff nonEmpty /\ \/_i (p[c_i/x] /\ c_i \in set)
            val existsElem = tla.or(setCells.zip(predEs).map(elemWitnesses): _*)
            tla.equiv(pred, tla.and(nonEmpty, existsElem))
          } else {
            // \A x \in S: p holds iff empty \/ /\_i (~p[c_i/x] \/ ~c_i \in set)
            val allElem = tla.and(setCells.zip(predEs).map(elemSatisfies): _*)
            tla.equiv(pred, tla.or(empty, allElem))
          }

        rewriter.solverContext.assertGroundExpr(iff)

        predState.setRex(pred)
          .setTheory(BoolTheory())
          .setBinding(predState.binding - boundVar) // forget the binding to x, but not the other bindings!
      }

    rewriter.coerce(finalState, state.theory)
  }

  private def freeExistsInSet(setState: SymbState, boundVar: String, predEx: TlaEx, set: ArenaCell) = {
    val setCells = setState.arena.getHas(set)
    if (setCells.isEmpty) {
      // \E x \in {}... is FALSE
      setState.setTheory(BoolTheory()).setRex(NameEx(rewriter.solverContext.falseConst))
    } else {
      freeExistsInNonEmptySet(setState, boundVar, predEx, set, setCells)
    }
  }

  // introduce a Skolem constant for a free-standing existential quantifier:
  // that is, rewrite, \E x \in S: P(x) as S /= {} /\ P(c) for a constant c picked from S
  private def freeExistsInNonEmptySet(setState: SymbState, boundVar: String, predEx: TlaEx,
                         set: ArenaCell, setCells: List[ArenaCell]) = {
    rewriter.solverContext.log("; free existential rule over a finite set")
    // pick an arbitrary witness
    val pickState = pickRule.pick(set, setState)
    val pickedCell = pickState.arena.findCellByNameEx(pickState.ex)
    // enforce that the witness satisfies the predicate
    val extendedBinding = pickState.binding + (boundVar -> pickedCell)
    // predState.ex contains the predicate applied to the witness
    val predState = rewriter.rewriteUntilDone(pickState
      .setTheory(BoolTheory()).setRex(predEx).setBinding(extendedBinding))
    val predWitness = predState.ex

    // \E x \in S: p holds iff predWitness /\ S /= {}
    val exPred = NameEx(rewriter.solverContext.introBoolConst())
    val notEmpty = tla.or(setCells.map(e => tla.in(e, set)): _*)
    val iff = tla.equiv(exPred, tla.and(predWitness, notEmpty))
    rewriter.solverContext.assertGroundExpr(iff)

    predState.setRex(exPred)
      .setTheory(BoolTheory())
      .setBinding(predState.binding - boundVar) // forget the binding to x, but not the other bindings!
  }

  // Introduce a Skolem constant for a free-standing existential quantifier:
  // In case of SUBSET(S), it is really easy: we have to enforce that a witness is a subset of S.
  // A powerset is never empty, so we do not have to worry about this case.
  private def freeExistsInPowerset(setState: SymbState, boundVar: String, predEx: TlaEx, set: ArenaCell) = {
    rewriter.solverContext.log("; free existential rule over a powerset")
    // pick an arbitrary witness
    val pickState = pickRule.pick(set, setState)
    val pickedCell = pickState.arena.findCellByNameEx(pickState.ex)
    // enforce that the witness satisfies the predicate
    val extendedBinding = pickState.binding + (boundVar -> pickedCell)
    // predState.ex contains the predicate applied to the witness
    val predState = rewriter.rewriteUntilDone(pickState
      .setTheory(BoolTheory()).setRex(predEx).setBinding(extendedBinding))
    val predWitness = predState.ex

    predState.setRex(predWitness)
      .setTheory(BoolTheory())
      .setBinding(predState.binding - boundVar) // forget the binding to x, but not the other bindings!
  }
}