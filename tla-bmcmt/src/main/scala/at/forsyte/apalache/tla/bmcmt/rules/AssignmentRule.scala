package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, FinFunSetT, FinSetT, PowSetT}
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}
import at.forsyte.apalache.tla.lir.convenience.tla

/**
  * Implements the rules: SE-ASSIGN{1,2,3}.
  * Similar to TLC, this is a special form of x' \in S operator that is treated
  * as an assignment of a value from S to the variable x'.
  *
  * TODO: add support for tuples!
  *
  * @author Igor Konnov
  */
class AssignmentRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val pickRule = new CherryPick(rewriter)

  override def isApplicable(state: SymbState): Boolean = {
    def isUnbound(name: String) =
      (!CellTheory().hasConst(name)
        && !BoolTheory().hasConst(name)
        && !IntTheory().hasConst(name)
        && !state.binding.contains(name + "'"))

    state.ex match {
      case OperEx(TlaSetOper.in, OperEx(TlaActionOper.prime, NameEx(name)), _) =>
        isUnbound(name)

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      // a common pattern x' \in {y} that deterministically assigns the value of y to x'
      case OperEx(TlaSetOper.in,
      OperEx(TlaActionOper.prime, NameEx(name)),
      OperEx(TlaSetOper.enumSet, rhs)) =>
        val nextState = rewriter.rewriteUntilDone(state.setRex(rhs).setTheory(CellTheory()))
        val rhsCell = nextState.arena.findCellByNameEx(nextState.ex)
        val finalState = nextState
          .setTheory(CellTheory())
          .setRex(state.arena.cellTrue().toNameEx)         // just return TRUE
          .setBinding(nextState.binding + (name + "'" -> rhsCell))  // bind the cell to the name
        rewriter.coerce(finalState, state.theory)

      // the general case
      case OperEx(TlaSetOper.in, OperEx(TlaActionOper.prime, NameEx(name)), set) =>
        // switch to cell theory
        val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(set))
        val setCell = setState.arena.findCellByNameEx(setState.ex)
        val elemCells = setState.arena.getHas(setCell)
        val finalState =
          if (setCell.cellType.isInstanceOf[FinSetT] && elemCells.isEmpty) {
            // nothing to pick from an empty set, return false
            setState.setTheory(CellTheory()).setRex(setState.arena.cellFalse().toNameEx)
          } else {
            setCell.cellType match {
              case PowSetT(_) | FinFunSetT(_, _) =>
                // these sets are never empty
                var nextState = pickRule.pick(setCell, setState)
                val pickedCell = nextState.asCell
                nextState
                  .setTheory(CellTheory())
                  .setRex(nextState.arena.cellTrue().toNameEx) // always true
                  .setBinding(nextState.binding + (name + "'" -> pickedCell)) // bind the picked cell to the name

              case FinSetT(_) =>
                // choose an oracle with the default case oracle = N, when the set is empty
                var nextState = pickRule.newOracleWithDefault(setState, setCell, elemCells)
                val oracle = nextState.asCell
                pickRule.constrainOracleWithIn(oracle, setCell, elemCells)
                // pick an arbitrary witness
                nextState = pickRule.pickByOracle(nextState, oracle.toNameEx, elemCells)
                val pickedCell = nextState.asCell
                // introduce a Boolean result that equals true unless the set is empty
                nextState = nextState.appendArenaCell(BoolT())
                val result = nextState.arena.topCell.toNameEx
                rewriter.solverContext.assertGroundExpr(tla.eql(result, tla.neql(oracle.toNameEx, tla.int(elemCells.size))))

                nextState
                  .setTheory(CellTheory())
                  .setRex(result) // true as soon as S /= {}
                  .setBinding(nextState.binding + (name + "'" -> pickedCell)) // bind the picked cell to the name
            }
          }

        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
