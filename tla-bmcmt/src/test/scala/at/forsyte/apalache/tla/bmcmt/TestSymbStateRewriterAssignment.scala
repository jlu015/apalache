package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.types.tsa._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.{SortedSet, TreeMap}

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterAssignment extends RewriterBase {
  test("""SE-IN-ASSIGN1(int): x' \in {1, 2} ~~> TRUE and [x -> $C$k]""") {
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(CellTheory().hasConst(name))
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    assert(solverContext.sat()) // no contradiction introduced
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(boundCell, tla.int(1)))
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(boundCell, tla.int(2)))
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(boundCell, tla.int(3)))
    assertUnsatOrExplain(rewriter, nextState) // should not be possible
  }

  test("""SE-IN-ASSIGN1(int): x' \in {} ~~> FALSE""") {
    val assign = tla.in(tla.prime(tla.name("x")), tla.enumSet())

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(arena.cellFalse().toString == name)
        assert(nextState.binding.isEmpty)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-IN-ASSIGN1(int): x' \in {1} /\ x' = 1 ~~> TRUE and [x -> $C$k]""") {
    val set = tla.enumSet(tla.int(1))
    val assign = tla.in(tla.prime(tla.name("x")), set)
    val and = tla.and(assign, tla.eql(tla.prime(tla.name("x")), tla.int(1)))

    val state = new SymbState(and, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(BoolTheory().hasConst(name))
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    assert(solverContext.sat()) // no contradiction introduced
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(!solverContext.sat())
  }

  test("""SE-IN-ASSIGN1(set): x' \in {{1, 2}, {2, 3}} ~~> TRUE and [x -> $C$k]""") {
    val set = tla.enumSet(tla.enumSet(tla.int(1), tla.int(2)),
      tla.enumSet(tla.int(2), tla.int(3)))
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(CellTheory().hasConst(name))
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    // no contradiction introduced
    assert(solverContext.sat())
    // may equal to {1, 2}
    rewriter.push()
    val eq12 = tla.eql(boundCell, tla.enumSet(tla.int(1), tla.int(2)))
    val eqState12 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {2, 3}
    rewriter.push()
    val eq23 = tla.eql(boundCell, tla.enumSet(tla.int(2), tla.int(3)))
    val eqState23 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq23))
    solverContext.assertGroundExpr(eqState23.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to {1, 3}
    rewriter.push()
    val eq13 = tla.eql(boundCell, tla.enumSet(tla.int(1), tla.int(3)))
    val eqState13 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain(rewriter, eqState13) // should not be possible
  }

  test("""SE-IN-ASSIGN1(fun): x' \in {[x \in BOOLEAN |-> 0], [x \in BOOLEAN |-> 1]} ~~> TRUE and [x -> $C$k]""") {
    val fun0 = tla.funDef(tla.int(0), tla.name("x"), tla.booleanSet())
    val fun1 = tla.funDef(tla.int(1), tla.name("x"), tla.booleanSet())
    val fun2 = tla.funDef(tla.int(2), tla.name("x"), tla.booleanSet())
    val set = tla.enumSet(fun0, fun1)
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(CellTheory().hasConst(name))
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    // no contradiction introduced
    assert(solverContext.sat())
    // may equal to fun0
    rewriter.push()
    val eqFun0 = tla.eql(boundCell, fun0)
    val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun0))
    solverContext.assertGroundExpr(eqStateFun0.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to fun1
    rewriter.push()
    val eqFun1 = tla.eql(boundCell, fun1)
    val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun1))
    solverContext.assertGroundExpr(eqStateFun1.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to fun2
    rewriter.push()
    val eqFun2 = tla.eql(boundCell, fun2)
    val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun2))
    solverContext.assertGroundExpr(eqStateFun2.ex)
    assertUnsatOrExplain(rewriter, eqStateFun2) // should not be possible
  }

  test("""SE-IN-ASSIGN1(funset): x' \in [BOOLEAN -> {0, 1}] ~~> TRUE and [x -> $C$k]""") {
    val fun0 = tla.funDef(tla.int(0), tla.name("x"), tla.booleanSet())
    val fun1 = tla.funDef(tla.int(1), tla.name("x"), tla.booleanSet())
    val fun2 = tla.funDef(tla.int(2), tla.name("x"), tla.booleanSet())
    val set = tla.funSet(tla.booleanSet(), tla.enumSet(tla.int(0), tla.int(1)))
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(CellTheory().hasConst(name))
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    // no contradiction introduced
    assert(solverContext.sat())
    // may equal to fun0
    rewriter.push()
    val eqFun0 = tla.eql(boundCell, fun0)
    val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun0))
    solverContext.assertGroundExpr(eqStateFun0.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to fun1
    rewriter.push()
    val eqFun1 = tla.eql(boundCell, fun1)
    val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun1))
    solverContext.assertGroundExpr(eqStateFun1.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to fun2
    rewriter.push()
    val eqFun2 = tla.eql(boundCell, fun2)
    val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(eqFun2))
    solverContext.assertGroundExpr(eqStateFun2.ex)
    assertUnsatOrExplain(rewriter, eqStateFun2) // should not be possible
  }

  test("""SE-IN-ASSIGN1(funset): x' \in [0..(5 - 1) ~~> {FALSE, TRUE}] ~~> TRUE and [x -> $C$k]""") {
    val domain = tla.dotdot(tla.int(0), tla.minus(tla.int(5), tla.int(1)))
    val set = tla.funSet(domain, tla.enumSet(tla.bool(false), tla.bool(true)))
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(CellTheory().hasConst(name))
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }
  }

  test("""SE-IN-ASSIGN1(tuple): x' \in {<<1, FALSE, {1, 3}>>, <<2, TRUE, {4}>>} ~~> [x -> $C$k]""") {
    val set1 = tla.enumSet(tla.int(1), tla.int(3))
    val tuple1 = tla.tuple(tla.int(1), tla.bool(false), set1)
    val set2 = tla.enumSet(tla.int(4))
    val tuple2 = tla.tuple(tla.int(2), tla.bool(true), set2)
    val set = tla.enumSet(tuple1, tuple2)
    val assign = tla.in(tla.prime(tla.name("x")), set)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.binding("x'")
        assert(TupleT(List(IntT(), BoolT(), FinSetT(IntT()))) == cell.cellType)

        val membershipTest =
          tla.and(tla.in(tla.appFun(tla.prime(tla.name("x")), tla.int(1)),
            tla.enumSet(tla.int(1), tla.int(2))),
            tla.in(tla.appFun(tla.prime(tla.name("x")), tla.int(2)),
              tla.enumSet(tla.bool(false), tla.bool(true))),
            tla.in(tla.appFun(tla.prime(tla.name("x")), tla.int(3)),
              tla.enumSet(set1, set2))
          ) ///

        assertTlaExAndRestore(rewriter, nextState.setRex(membershipTest))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-IN-ASSIGN1(record): x' \in {{"a" -> 1, "b" -> FALSE}, {"a" -> 2, "b" -> TRUE, "c" -> {3, 4}}} ~~> [x -> $C$k]""") {
    // records in a set can have different -- although compatible -- sets of keys
    val record1 = tla.enumFun(tla.str("a"), tla.int(1),
      tla.str("b"), tla.bool(false))
    val set2 = tla.enumSet(tla.int(3), tla.int(4))
    val record2 = tla.enumFun(tla.str("a"), tla.int(2),
      tla.str("b"), tla.bool(true), tla.str("c"), set2)
    val recordSet = tla.enumSet(record1, record2)
    val assign = tla.in(tla.prime(tla.name("x")), recordSet)

    val state = new SymbState(assign, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.binding("x'")
        assert(cell.cellType.isInstanceOf[RecordT])
        assert(cell.cellType.asInstanceOf[RecordT].fields
          == TreeMap("a" -> IntT(), "b" -> BoolT(), "c" -> FinSetT(IntT())))

        val membershipTest =
          tla.and(tla.in(tla.appFun(tla.prime(tla.name("x")), tla.str("a")),
            tla.enumSet(tla.int(1), tla.int(2))),
            tla.in(tla.appFun(tla.prime(tla.name("x")), tla.str("b")),
              tla.enumSet(tla.bool(false), tla.bool(true))),
            tla.in(tla.appFun(tla.prime(tla.name("x")), tla.str("c")),
              tla.enumSet(set2))
          ) ///

        assertTlaExAndRestore(rewriter, nextState.setRex(membershipTest))

        // if we assume that result["a"] = 2, we should get result["b"] = TRUE, and result["c"] = { 3, 4 }
        rewriter.push()
        val assumption = tla.eql(tla.appFun(tla.prime(tla.name("x")), tla.str("a")), tla.int(2))
        val assumState = assumeTlaEx(rewriter, nextState.setRex(assumption))

        val bIsTrue = tla.eql(tla.appFun(tla.prime(tla.name("x")), tla.str("b")), tla.bool(true))
        val cIsSet2 = tla.eql(tla.appFun(tla.prime(tla.name("x")), tla.str("c")), set2)
        val assertion = tla.and(bIsTrue, cIsSet2)
        assertTlaExAndRestore(rewriter, assumState.setRex(assertion))
        rewriter.pop()

        // if we assume that result["a"] = 1, we should get DOMAIN result = {"a", "b"}
        rewriter.push()
        val assumption2 = tla.eql(tla.appFun(tla.prime(tla.name("x")), tla.str("a")), tla.int(1))
        val assumeState2 = assumeTlaEx(rewriter, nextState.setRex(assumption2))
        val (newArena, expectedDom) =
          rewriter.recordDomainCache.getOrCreate(assumeState2.arena, SortedSet("a", "b"))
        val domEq = tla.eql(expectedDom, tla.dom(tla.prime(tla.name("x"))))
        assertTlaExAndRestore(rewriter, assumeState2.setArena(newArena).setRex(domEq))
        // and check that the record equals to the expected one
        val eq = tla.eql(record1, tla.prime(tla.name("x")))
        assertTlaExAndRestore(rewriter, assumeState2.setRex(eq))
        rewriter.pop()

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
