package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.lir.oper.TlaSeqOper

/**
  * Sequence operations: Head, Tail, Len, SubSeq, and Append.
  *
  * @author Igor Konnov
  */
class SeqOpsRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new CherryPick(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSeqOper.head, _) => true
      case OperEx(TlaSeqOper.tail, _) => true
      case OperEx(TlaSeqOper.subseq, _, _, _) => true
      case OperEx(TlaSeqOper.len, _) => true
      case OperEx(TlaSeqOper.append, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSeqOper.head, seq) =>
        rewriter.rewriteUntilDone(state.setRex(tla.appFun(seq, tla.int(1))))

      case OperEx(TlaSeqOper.len, seq) =>
        translateLen(state, seq)

      case OperEx(TlaSeqOper.tail, seq) =>
        translateTail(state, seq)

      case OperEx(TlaSeqOper.subseq, seq, newStart, newEnd) =>
        translateSubSeq(state, seq, newStart, newEnd)

      case OperEx(TlaSeqOper.append, seq, newElem) =>
        translateAppend(state, seq, newElem)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def translateTail(state: SymbState, seq: TlaEx) = {
    var nextState = rewriter.rewriteUntilDone(state.setRex(seq).setTheory(CellTheory()))
    val seqCell = nextState.asCell
    val cells = nextState.arena.getHas(seqCell)
    val start = cells.head
    // increment start
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.plus(tla.int(1), start)))
    val newStart = nextState.asCell
    // introduce a new sequence that is different from seq in that the 0th element equals to newStart
    nextState = nextState.appendArenaCell(seqCell.cellType)
    val newSeqCell = nextState.arena.topCell
    nextState = nextState.setArena(nextState.arena.appendHas(newSeqCell, newStart +: cells.tail))
    nextState.setRex(newSeqCell).setTheory(CellTheory())
  }

  private def translateSubSeq(state: SymbState, seq: TlaEx, newStartEx: TlaEx, newEndEx: TlaEx) = {
    var nextState = rewriter.rewriteUntilDone(state.setRex(seq).setTheory(CellTheory()))
    val seqCell = nextState.asCell
    val cells = nextState.arena.getHas(seqCell)
    val start = cells.head

    // TODO: check that the new range is allowed?
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.plus(start, tla.minus(newStartEx, tla.int(1)))))
    val newStart = nextState.asCell
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.plus(start, newEndEx)))
    val newEnd = nextState.asCell
    // introduce a new sequence that whose start and end are updated as required
    nextState = nextState.appendArenaCell(seqCell.cellType)
    val newSeqCell = nextState.arena.topCell
    nextState = nextState.setArena(nextState.arena.appendHas(newSeqCell, newStart :: newEnd +: cells.tail.tail))
    nextState.setRex(newSeqCell).setTheory(CellTheory())
  }

  private def translateAppend(state: SymbState, seq: TlaEx, newElem: TlaEx) = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _
    var nextState = rewriter.rewriteUntilDone(state.setRex(seq).setTheory(CellTheory()))
    val seqCell = nextState.asCell
    val cells = nextState.arena.getHas(seqCell)
    val start = cells.head
    val end = cells.tail.head
    val oldElems = cells.tail.tail
    nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.plus(tla.int(1), end)))
    val newEnd = nextState.asCell
    nextState = rewriter.rewriteUntilDone(nextState.setRex(newElem).setTheory(CellTheory()))
    val newElemCell = nextState.asCell
    // as we do not know the actual values of the range [start, end),
    // pick from the original value s[i] and the new element, and restrict the choice
    // based on the actual values of start and end
    def transform(oldElemCell: ArenaCell, no: Int): ArenaCell = {
      nextState = nextState.appendArenaCell(IntT())
      val oracle = nextState.arena.topCell.toNameEx
      solverAssert(tla.ge(oracle, tla.int(0)))
      solverAssert(tla.le(oracle, tla.int(1)))
      nextState = picker.pickByOracle(nextState, oracle, Seq(oldElemCell, newElemCell))
      // pick the element from the old sequence: start <= no /\ no < end => oracle = 0
      solverAssert(tla.impl(tla.and(tla.le(start, tla.int(no)), tla.lt(tla.int(no), end)),
        tla.eql(oracle, tla.int(0))))
      // pick the element from the new sequence: no = end => oracle = 1
      solverAssert(tla.impl(tla.eql(tla.int(no), end), tla.eql(oracle, tla.int(1))))
      // the other elements are unrestricted, give some freedom to the solver
      nextState.asCell
    }

    val transformedCells = oldElems.zipWithIndex map (transform _).tupled
    val newCells = (newElemCell :: transformedCells.reverse).reverse

    // introduce a new sequence that statically has one more element
    nextState = nextState.appendArenaCell(seqCell.cellType)
    val newSeqCell = nextState.arena.topCell
    nextState = nextState.setArena(nextState.arena.appendHas(newSeqCell, start :: newEnd +: newCells))
    nextState.setRex(newSeqCell).setTheory(CellTheory())
  }

  private def translateLen(state: SymbState, seq: TlaEx) = {
    var nextState = rewriter.rewriteUntilDone(state.setRex(seq).setTheory(CellTheory()))
    val cells = nextState.arena.getHas(nextState.asCell)
    val start = cells.head
    val end = cells.tail.head
    // just return end - start
    rewriter.rewriteUntilDone(nextState.setRex(tla.minus(end, start)))
  }
}
