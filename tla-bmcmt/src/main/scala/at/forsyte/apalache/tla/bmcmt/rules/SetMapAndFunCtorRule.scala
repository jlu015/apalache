package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.types.TypeException
import at.forsyte.apalache.tla.types.tsa._

/**
  * Implements the rules: SE-SET-MAP[1-2] and SE-FUN-CTOR[1-2].
  *
  * Since set map and function constructors have a lot in common, we implement them in the same class.
  *
  * @author Igor Konnov
  */
class SetMapAndFunCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.map, _*) => true
      case OperEx(TlaFunOper.funDef, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.funDef, mapEx, NameEx(varName), setEx) =>
        rewriteFunCtor(state, mapEx, varName, setEx)

      case OperEx(TlaSetOper.map, mapEx, NameEx(varName), setEx) =>
        rewriteSetMap(state, mapEx, varName, setEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def rewriteSetMap(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx) = {
    // rewrite the set expression into a memory cell
    val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(setEx))
    val oldSetCell = setState.arena.findCellByNameEx(setState.ex)
    // unfold the set and produce map every potential element to a cell
    val oldCells = setState.arena.getHas(oldSetCell)

    val (newState: SymbState, newCells: Seq[ArenaCell], elemType: CellT) =
      mapCells(setState, mapEx, varName, setEx, oldCells)

    // introduce a new set
    val arena = newState.arena.appendCell(FinSetT(elemType))
    val newSetCell = arena.topCell
    val newArena = newCells.foldLeft(arena)((a, e) => a.appendHas(newSetCell, e))

    // require each new cell to be in the new set iff the old cell was in the old set
    def addCellCons(oldCell: ArenaCell, newCell: ArenaCell): Unit = {
      val inNewSet = OperEx(TlaSetOper.in, newCell.toNameEx, newSetCell.toNameEx)
      val inOldSet = OperEx(TlaSetOper.in, oldCell.toNameEx, oldSetCell.toNameEx)
      val ifAndOnlyIf = OperEx(TlaOper.eq, inNewSet, inOldSet)
      rewriter.solverContext.assertGroundExpr(ifAndOnlyIf)
    }

    // add SMT constraints
    for ((cell, pred) <- oldCells zip newCells)
      addCellCons(cell, pred)

    // that's it
    val finalState =
      newState.setTheory(CellTheory())
        .setArena(newArena).setRex(newSetCell.toNameEx)
    rewriter.coerce(finalState, state.theory)
  }

  private def rewriteFunCtor(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx) = {
    // rewrite the set expression into a memory cell
    val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(setEx))
    val domainCell = setState.arena.findCellByNameEx(setState.ex)
    // unfold the set and produce map every potential element to a cell
    val domainCells = setState.arena.getHas(domainCell)

    val (newState: SymbState, resultCells: Seq[ArenaCell], elemType: CellT) =
      mapCells(setState, mapEx, varName, setEx, domainCells)

    val funType = FunT(domainCell.cellType, elemType)
    // introduce a co-domain cell
    var arena = newState.arena.appendCell(funType)
    val funCell = arena.topCell
    val arena2 = arena.appendCell(FinSetT(elemType)) // co-domain is a finite set of type elemType
    val codomainCell = arena2.topCell
    arena = arena2.setDom(funCell, domainCell).setCdm(funCell, codomainCell)
    arena = resultCells.foldLeft(arena) ((a, e) => a.appendHas(codomainCell, e))
    // associate a function constant with the function cell
    rewriter.solverContext.declareCellFun(funCell.name, funType.argType, funType.resultType)

    // associate a value of the uninterpreted function with a cell
    def addCellCons(argCell: ArenaCell, resultCell: ArenaCell): Unit = {
      val inDomain = tla.in(argCell, domainCell)
      val funEqResult = tla.eql(resultCell, tla.appFun(funCell, argCell)) // this is translated as function application
      val inDomainImpliesResult = tla.impl(inDomain, funEqResult)
      rewriter.solverContext.assertGroundExpr(inDomainImpliesResult)
      // the result unconditionally belongs to the co-domain
      rewriter.solverContext.assertGroundExpr(tla.in(resultCell, codomainCell))
    }

    // add SMT constraints
    for ((cell, pred) <- domainCells zip resultCells)
      addCellCons(cell, pred)

    // that's it
    val finalState =
      newState.setTheory(CellTheory())
        .setArena(arena).setRex(funCell.toNameEx)
    rewriter.coerce(finalState, state.theory)
  }

  private def mapCells(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx, oldCells: Seq[ArenaCell]) = {
    // similar to SymbStateRewriter.rewriteSeqUntilDone and SetFilterRule
    def process(st: SymbState, seq: Seq[ArenaCell]): (SymbState, Seq[TlaEx]) = {
      seq match {
        case Seq() =>
          (st, List())

        case (cell: ArenaCell) :: tail =>
          val (ts: SymbState, nt: List[TlaEx]) = process(st, tail)
          val newBinding = ts.binding + (varName -> cell)
          val cellState = new SymbState(mapEx, CellTheory(), ts.arena, newBinding)
          // add [cell/x]
          val ns = rewriter.rewriteUntilDone(cellState)
          (ns.setBinding(ts.binding), ns.ex :: nt) // reset binding and add the new expression in the head
      }
    }

    // compute mappings for all the cells (some of them may coincide, that's fine)
    val (newState: SymbState, newEs: Seq[TlaEx]) = process(state, oldCells)
    val newCells = newEs.map(newState.arena.findCellByNameEx)
    // get the cell types
    val elemType =
      newCells.map(_.cellType).toSet.toList match {
        case List() =>
          UnknownT()

        case list @_ =>
          val unifier = unify(list :_*)
          if (unifier.isDefined) {
            unifier.get
          } else {
            throw new TypeException(s"No unifying type for ${list.mkString(", ")} (when rewriting $mapEx)")
          }
      }

    (newState, newCells, elemType)
  }
}
