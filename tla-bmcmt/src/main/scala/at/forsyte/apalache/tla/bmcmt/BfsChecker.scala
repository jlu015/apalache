package at.forsyte.apalache.tla.bmcmt

import java.io.{FileWriter, PrintWriter, StringWriter}

import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, FreeExistentialsStoreImpl}
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import com.typesafe.scalalogging.LazyLogging

import scala.util.matching.Regex

/**
  * A bounded model checker using SMT. For each step, this checker applies all possible symbolic transitions
  * and then merges the result. Hence, it is similar to breadth-first search. The major limitation of this search is
  * that for each step, all symbolic transitions should agree on the types of assigned variables.
  *
  * We expect the invariant to be negated and written over prime variables.
  *
  * @author Igor Konnov
  */
class BfsChecker(typeFinder: TypeFinder[CellT], frexStore: FreeExistentialsStoreImpl,
                 exprGradeStore: ExprGradeStore, sourceStore: SourceStore, checkerInput: CheckerInput,
                 stepsBound: Int, filter: String,
                 debug: Boolean = false, profile: Boolean = false,
                 checkRuntime: Boolean = false) extends Checker with LazyLogging {

  import Checker._

  class CancelSearchException(val outcome: Outcome.Value) extends Exception

  /**
    * A stack of the symbolic states that might constitute a counterexample (the last state is on top).
    */
  private var stack: List[(SymbState, ArenaCell)] = List()
  private val solverContext: SolverContext =
    new Z3SolverContext(debug, profile)
  //    new PreproSolverContext(new Z3SolverContext(debug, profile))

  private val rewriter: SymbStateRewriterImpl = new SymbStateRewriterImpl(solverContext, typeFinder, exprGradeStore)
  rewriter.freeExistentialsStore = frexStore
  rewriter.introFailures = checkRuntime

  private val stepFilters: Seq[String] = if (filter == "") Seq() else filter.split(",")
  /**
    * A list of transitions that are enabled at every step
    */
  private var enabledList: Seq[Seq[Int]] = Seq()

  /**
    * Check all executions of a TLA+ specification up to a bounded number of steps.
    *
    * @return a verification outcome
    */
  def run(): Outcome.Value = {
    val initialArena = Arena.create(solverContext)
    val dummyState = new SymbState(initialArena.cellTrue().toNameEx,
      CellTheory(), initialArena, new Binding)
    val outcome =
      try {
        var state = makeOneStep(0, dummyState, checkerInput.initTransitions)
        shiftTypes() // for each x', assign type(x) to be type(x'), forget x'
        for (i <- 1 to stepsBound) {
          // checking for deadlocks is not so easy in our encoding
          //        checkForDeadlocks(i, state, nextStates)
          state = makeOneStep(i, state, checkerInput.nextTransitions)
          shiftTypes() // for each x', assign type(x) to be type(x'), forget x'
        }
        Outcome.NoError
      } catch {
        case err: CheckerException =>
          // try to get any info about the problematic source location
          printRewriterSourceLoc()
          throw err

        case ce: CancelSearchException =>
          ce.outcome
      }
    // flush the logs
    rewriter.dispose()
    outcome
  }

  private def printRewriterSourceLoc(): Unit = {
    def getSourceLocation(ex: TlaEx) = sourceStore.find(ex.ID)

    rewriter.getRewritingStack().find(getSourceLocation(_).isDefined) match {
      case None =>
        logger.error("Unable find the source of the problematic expression")

      case Some(ex) =>
        val loc = getSourceLocation(ex).get
        logger.error(s"The problem occurs around the source location $loc")
    }
  }

  // does the transition number satisfy the given filter at the given step?
  private def stepMatchesFilter(stepNo: Int, transitionNo: Int): Boolean = {
    if (stepFilters.size <= stepNo) {
      true // no filter applied
    } else {
      val stepRegex = new Regex(stepFilters(stepNo))
      transitionNo.toString match {
        case stepRegex() => true
        case _ => false
      }
    }
  }

  private def makeOneStep(stepNo: Int, startingState: SymbState, transitions: List[TlaEx]): SymbState = {
    // first, find all the feasible transition and check the invariant for each transition
    logger.info("Step %d, applying %d transition(s) and checking for errors".format(stepNo, transitions.length))

    def filterEnabledAndCheckErrors(state: SymbState, ts: List[TlaEx], transitionNo: Int): List[(TlaEx, Int)] = {
      ts match {
        case List() => List()

        case tran :: tail =>
          if (!stepMatchesFilter(stepNo, transitionNo)) {
            filterEnabledAndCheckErrors(state, tail, transitionNo + 1) // just skip this transition
          } else {
            rewriter.push()
            val erased = state.setBinding(forgetPrimed(state.binding))
            val nextState = applyTransition(stepNo, erased, tran, transitionNo, checkForErrors = true)
            rewriter.exprCache.disposeActionLevel() // leave only the constants
            rewriter.pop() // forget all the constraints that were generated by the transition
            if (nextState.isDefined) {
              (tran, transitionNo) +: filterEnabledAndCheckErrors(state, tail, transitionNo + 1)
            } else {
              filterEnabledAndCheckErrors(state, tail, transitionNo + 1)
            }
          }
      }
    }

    val savedVarTypes = rewriter.typeFinder.getVarTypes // save the variable types before applying the transitions
    val enabled = filterEnabledAndCheckErrors(startingState, transitions, 0)
    enabledList :+= enabled map (_._2) // put it on stack
    dumpEnabledMap()

    // second, apply the enabled transitions and collect their effects
    logger.info("Step %d, collecting %d enabled transition(s)".format(stepNo, enabled.length))

    def applyAllEnabled(state: SymbState, ts: List[TlaEx], transitionNo: Int): List[SymbState] =
      ts match {
        case List() =>
          List()

        case tran :: tail =>
          val erased = state.setBinding(forgetPrimed(state.binding))
          val nextState = applyTransition(stepNo, erased, tran, transitionNo, checkForErrors = false)
          rewriter.exprCache.disposeActionLevel() // leave only the constants
          if (nextState.isDefined) {
            nextState.get +: applyAllEnabled(nextState.get, tail, transitionNo + 1)
          } else {
            applyAllEnabled(state, tail, transitionNo + 1)
          }
      }

    rewriter.typeFinder.reset(savedVarTypes) // restore the variable types to apply the enabled transitions once again
    val nextStates = applyAllEnabled(startingState, enabled map (_._1), 0)
    /*
    // debugging info that really slows down model checking
    val (nconst, ntotal) = rewriter.lazyEq.countConstantEqualities()
    logger.info(s"Found $nconst of $ntotal constant equalities in the equality cache")
    */

    if (nextStates.isEmpty) {
      logger.error(s"No next transition applicable on step $stepNo. Deadlock detected.")
      if (solverContext.sat()) {
        logger.error("Check an execution leading to a deadlock state in counterexample.txt")
        dumpCounterexample()
      } else {
        logger.error("No counterexample found")
      }
      throw new CancelSearchException(Outcome.Deadlock)
    } else if (nextStates.lengthCompare(1) == 0) {
      // the only next state -- return it
      // introduce the transition just for the record
      val onlyState = nextStates.head
      val newArena = onlyState.arena.appendCell(IntT())
      val transitionIndex = newArena.topCell
      solverContext.assertGroundExpr(tla.eql(transitionIndex.toNameEx, tla.int(0)))
      val resultingState = onlyState.setBinding(shiftBinding(onlyState.binding))
      stack = (resultingState, transitionIndex) +: stack
      solverContext.assertGroundExpr(onlyState.ex)
      resultingState.setArena(newArena)
    } else {
      // pick an index j \in { 0..k } of the fired transition
      val lastState = nextStates.last // the last state has the largest arena
      val newArena = lastState.arena.appendCell(IntT())
      val transitionIndex = newArena.topCell // it also the oracle for picking cells

      def transitionFired(state: SymbState, index: Int): TlaEx =
      // it is tempting to use <=> instead of => here, but this might require from an inactive transition
      // to be completely disabled, while we just say that it is not picked
        tla.impl(tla.eql(transitionIndex.toNameEx, tla.int(index)), state.ex)

      // the bound on j will be rewritten in pickState
      val leftBound = tla.le(tla.int(0), transitionIndex.toNameEx)
      val rightBound = tla.lt(transitionIndex.toNameEx, tla.int(nextStates.length))
      solverContext.assertGroundExpr(tla.and(leftBound, rightBound))
      solverContext.assertGroundExpr(tla.and(nextStates.zipWithIndex.map((transitionFired _).tupled): _*))

      // glue the computed states S0, ..., Sk together:
      // for every variable x, pick c_x from { S1[x], ..., Sk[x] }
      //   and require \A i \in { 0.. k-1}. j = i => c_x = Si[x]
      // Then, the final state binds x -> c_x for every x \in Vars
      val vars = forgetNonPrimed(lastState.binding).keySet
      var finalState = lastState.setBinding(forgetPrimed(lastState.binding)).setArena(newArena).setRex(tla.bool(true))
      if (nextStates.map(_.binding).exists(b => forgetNonPrimed(b).keySet != vars)) {
        throw new InternalCheckerError(s"Next states disagree on the set of assigned variables (step $stepNo)")
      }

      def pickVar(x: String): ArenaCell = {
        val toPickFrom = nextStates map (_.binding(x))
        finalState = new CherryPick(rewriter).pickByOracle(finalState, transitionIndex.toNameEx, toPickFrom)
        finalState.asCell
      }

      val finalBinding = Binding(vars.toSeq map (n => (n, pickVar(n))): _*)
      finalState = finalState.setBinding(shiftBinding(finalBinding))
      if (!solverContext.sat()) {
        throw new InternalCheckerError(s"Error picking next variables (step $stepNo). Report a bug.")
      }
      // that is the result of this step
      stack = (finalState, transitionIndex) +: stack
      finalState
    }
  }

  private def applyTransition(stepNo: Int, state: SymbState, transition: TlaEx,
                              transitionNo: Int, checkForErrors: Boolean): Option[SymbState] = {
    rewriter.push()
    logger.debug("Step #%d, transition #%d, SMT context level %d."
      .format(stepNo, transitionNo, rewriter.contextLevel))
    logger.debug("Finding types of the variables...")
    checkTypes(transition)
    solverContext.log("; ------- STEP: %d, STACK LEVEL: %d {".format(stepNo, rewriter.contextLevel))
    logger.debug("Applying rewriting rules...")
    val nextState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()).setRex(transition))
    rewriter.flushStatistics()
    if (checkForErrors) {
      logger.debug("Finished rewriting. Checking satisfiability of the pushed constraints.")
      if (!solverContext.sat()) {
        // this is a clear sign of a bug in one of the translation rules
        logger.debug("UNSAT after pushing transition constraints")
        throw new CheckerException("A contradiction introduced in rewriting. Report a bug.")
      }
    }
    if (!checkForErrors) {
      // assume no failure occurs
      val failPreds = state.arena.findCellsByType(FailPredT())
      failPreds.map(fp => tla.not(fp.toNameEx)) foreach solverContext.assertGroundExpr
      // just return the state
      Some(nextState)
    } else {
      rewriter.push()
      // assume the constraint constructed by this transition
      solverContext.assertGroundExpr(nextState.ex)
      // check whether this transition violates some assertions
      checkAssertionErrors(nextState)
      logger.debug("Checking satisfiability of the pushed constraints.")
      if (!solverContext.sat()) {
        // the current symbolic state is not feasible
        logger.debug("Transition #%d is not feasible. Skipped.".format(transitionNo))
        rewriter.pop()
        rewriter.pop()
        solverContext.log("; } ------- STEP: %d, STACK LEVEL: %d".format(stepNo, rewriter.contextLevel))
        None
      } else {
        // check the invariant right here
        checkInvariant(stepNo, nextState)
        // and then forget all these constraints!
        rewriter.pop() // forget about that the transition was taken
        solverContext.log("; } ------- STEP: %d, STACK LEVEL: %d".format(stepNo, rewriter.contextLevel))
        Some(nextState)
      }
    }
  }

  private def checkAssertionErrors(state: SymbState): Unit = {
    // Detecting runtime errors such as: assertion violation,
    // or function application outside its domain.
    // The crucial assumption here is that IF-THEN-ELSE activates runtime errors only
    // on the active branches, see IfThenElseRule.
    val failPreds = state.arena.findCellsByType(FailPredT())
    if (checkRuntime) {
      logger.debug("Checking for runtime errors")
      rewriter.push()
      solverContext.assertGroundExpr(tla.or(failPreds.map(_.toNameEx): _*))
      if (solverContext.sat()) {
        logger.error("The specification may produce a runtime error. Check the counterexample.")
        val activeFailures =
          failPreds.filter(fp => solverContext.evalGroundExpr(fp.toNameEx) == tla.bool(true))

        logger.error(s"The following failures are possible: %s.".format(activeFailures.mkString(", ")))
        activeFailures.foreach(fp => logger.error(rewriter.findMessage(fp.id)))

        dumpCounterexample()
        // dump everything in the log
        val writer = new StringWriter()
        new SymbStateDecoder(solverContext, rewriter).dumpArena(state, new PrintWriter(writer))
        solverContext.log(writer.getBuffer.toString)

        throw new CancelSearchException(Outcome.RuntimeError)
      }
      rewriter.pop()
      logger.debug("No runtime errors")
    }
    // assume no failure occurs
    failPreds.map(fp => tla.not(fp.toNameEx)) foreach solverContext.assertGroundExpr
  }

  private def checkForDeadlocks(stepNo: Int, state: SymbState, nextStates: List[SymbState]): Unit = {
    rewriter.push()
    solverContext.assertGroundExpr(tla.and(nextStates.map(e => tla.not(e.ex)): _*))
    if (solverContext.sat()) {
      val filename = dumpCounterexample()
      logger.error(s"Deadlock detected at step $stepNo. Check $filename")
      throw new CancelSearchException(Outcome.Deadlock)
    }
    rewriter.pop()
  }

  // TODO: This decomposition could be done at previous phases
  private def checkInvariantPiecewise(depth: Int, state: SymbState, notInv: TlaEx): Boolean = {
    // check disjuncts separately, in order to simplify the problem for SMT
    notInv match {
      case OperEx(TlaBoolOper.or, args@_*) =>
        args exists (a => checkInvariantPiecewise(depth, state, a))

      case OperEx(TlaBoolOper.exists, name, set, OperEx(TlaBoolOper.or, args@_*)) =>
        def oneExists(a: TlaEx) = {
          // this existential can be skolemized
          val ex = tla.exists(name, set, a)
          frexStore.store.add(ex.ID)
          ex
        }
        // use the equivalence \E x \in S: A \/ B <=> (\E x \in S: A) \/ (\E x \in S: B)
        args exists (a => checkInvariantPiecewise(depth, state, oneExists(a)))

      case ite@OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        // ITE(A, B, C) == A /\ B \/ ~A /\ B
        val pieces = Seq(tla.and(predEx, thenEx), tla.and(tla.not(predEx), elseEx))
        pieces exists (a => checkInvariantPiecewise(depth, state, a))

      case OperEx(TlaBoolOper.exists, name, set, OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx)) =>
        // \E x \in S: ITE(A, B, C) == (\E x \in S: A /\ B) \/ (\E x \in S: ~A /\ B)
        def oneExists(a: TlaEx) = {
          // this existential can be skolemized
          val ex = tla.exists(name, set, a)
          frexStore.store.add(ex.ID)
          ex
        }

        val pieces = Seq(oneExists(tla.and(predEx, thenEx)), oneExists(tla.and(tla.not(predEx), elseEx)))
        // use the equivalence \E x \in S: A \/ B <=> (\E x \in S: A) \/ (\E x \in S: B)
        pieces exists (a => checkInvariantPiecewise(depth, state, oneExists(a)))

      case _ =>
        logger.debug(s"Checking an invariant piece $notInv")
        rewriter.push()
        val notInvState = rewriter.rewriteUntilDone(state
          .setTheory(BoolTheory())
          .setRex(notInv))
        solverContext.assertGroundExpr(notInvState.ex)
        checkAssertionErrors(notInvState) // the invariant violation may introduce runtime errors
      val notInvSat = solverContext.sat()
        if (notInvSat) {
          val newArena = notInvState.arena.appendCell(IntT()) // FIXME
          val transitionIndex = newArena.topCell

          val finalState = notInvState.setArena(newArena).setBinding(shiftBinding(notInvState.binding))
          stack = (finalState, transitionIndex) +: stack
          val filename = dumpCounterexample()
          logger.error(s"Invariant is violated at depth $depth. Check the counterexample in $filename")
          // dump everything in the log
          val writer = new StringWriter()
          new SymbStateDecoder(solverContext, rewriter).dumpArena(notInvState, new PrintWriter(writer))
          solverContext.log(writer.getBuffer.toString)
          throw new CancelSearchException(Outcome.Error)
        }
        rewriter.pop()
        notInvSat
    }
  }

  private def checkInvariant(depth: Int, state: SymbState): SymbState = {
    checkAssertionErrors(state)
    if (checkerInput.notInvariant.isEmpty) {
      state
    } else {
      logger.debug("Checking the invariant")
      val notInv = checkerInput.notInvariant.get
      val savedTypes = rewriter.typeFinder.getVarTypes
      checkTypes(notInv)
      val notInvSat = checkInvariantPiecewise(depth, state, notInv)
      rewriter.typeFinder.reset(savedTypes) // forget about the types that were used to check the invariant
      state
    }
  }

  private def dumpCounterexample(): String = {
    val filename = "counterexample.txt"
    val writer = new PrintWriter(new FileWriter(filename, false))
    for (((state, transitionCell), i) <- stack.reverse.zipWithIndex) {
      val decoder = new SymbStateDecoder(solverContext, rewriter)
      val transition = decoder.decodeCellToTlaEx(state.arena, transitionCell)
      writer.println(s"State $i (from transition $transition):")
      writer.println("--------")
      val binding = decoder.decodeStateVariables(state)
      for ((name, ex) <- binding) {
        writer.println("%-15s ->  %s".format(name, UTFPrinter.apply(ex)))
      }
      writer.println("========\n")
    }
    writer.close()
    filename
  }

  private def checkTypes(expr: TlaEx): Unit = {
    typeFinder.inferAndSave(expr)
    if (typeFinder.getTypeErrors.nonEmpty) {
      def print_error(e: TypeInferenceError): Unit = {
        val locInfo =
          sourceStore.find(e.origin.safeId) match {
            case Some(loc) => loc.toString
            case None => "<unknown origin>"
          }
        val exStr = e.origin match {
          case OperEx(op, _*) => op.name + "(...)"
          case ex@_ => ex.toString()
        }
        logger.error("%s, %s, type error: %s".format(locInfo, exStr, e.explanation))
      }

      typeFinder.getTypeErrors foreach print_error
      throw new CancelSearchException(Outcome.Error)
    }
  }

  /**
    * Remove the non-primed variables and rename the primed variables to their non-primed versions.
    * After that, remove the type finder to contain the new types only.
    */
  private def shiftTypes(): Unit = {
    val types = typeFinder.getVarTypes
    val nextTypes = types.filter(_._1.endsWith("'")).map(p => (p._1.stripSuffix("'"), p._2))
    typeFinder.reset(nextTypes)
  }

  private def forgetPrimedTypes(): Unit = {
    val types = typeFinder.getVarTypes
    val unprimedTypes = types.filter(!_._1.endsWith("'"))
    typeFinder.reset(unprimedTypes)
  }

  // remove non-primed variables and rename primed variables to non-primed
  private def shiftBinding(binding: Binding): Binding = {
    forgetNonPrimed(binding)
      .map(p => (p._1.stripSuffix("'"), p._2))
  }

  // remove primed variables
  private def forgetPrimed(binding: Binding): Binding = {
    binding.filter(p => !p._1.endsWith("'"))
  }

  // remove non-primed variables
  private def forgetNonPrimed(binding: Binding): Binding = {
    binding.filter(p => p._1.endsWith("'"))
  }

  private def dumpEnabledMap(): Unit = {
    val filename = "enabled-map.txt"
    val writer = new PrintWriter(new FileWriter(filename, false))
    val transitionsCnt = checkerInput.nextTransitions.size
    writer.println("The map of enabled transitions:")
    val hrule = "----%s".format((0 until transitionsCnt map (_ => "-")) mkString "")
    writer.println(hrule)
    writer.println("    %s".format(0 until transitionsCnt map (i => ((i / 100) % 10).toString) mkString ""))
    writer.println("    %s".format(0 until transitionsCnt map (i => ((i / 10) % 10).toString) mkString ""))
    writer.println("    %s".format(0 until transitionsCnt map (i => (i % 10).toString) mkString ""))
    writer.println(hrule)
    for ((enabled, stepNo) <- enabledList.zipWithIndex) {
      val set = Set(enabled :_*)
      val line = 0 until transitionsCnt map (i => if (set.contains(i)) "*" else " ") mkString ""
      writer.println(s"%3d:%s".format(stepNo, line))
    }
    writer.println(hrule)
    writer.close()
  }
}
