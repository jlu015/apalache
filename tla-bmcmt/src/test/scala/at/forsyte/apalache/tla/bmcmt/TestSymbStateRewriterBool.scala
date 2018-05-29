package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.predef.TlaBoolSet
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx}
import at.forsyte.apalache.tla.types.tsa.BoolT
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterBool extends RewriterBase {

  test("SE-BOOL-FALSE [Cell]: FALSE ~~> $C$0") {
    val ex = ValEx(TlaFalse)
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$0")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-FALSE [Bool]: FALSE ~~> $B$0") {
    val ex = ValEx(TlaFalse)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx("$B$0") == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-SET-BOOLEAN: BOOLEAN ~~> c_BOOLEAN") {
    val state = new SymbState(ValEx(TlaBoolSet), CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$2")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-TRUE [Cell]: TRUE ~~> $C$1") {
    val ex = ValEx(TlaTrue)
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$1")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-TRUE [Bool]: TRUE ~~> $B$1") {
    val ex = ValEx(TlaTrue)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$B$1")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG1: ~(x \/ y) ~~> ~x /\ ~y""") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.or, NameEx("x"), NameEx("y")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.and,
          OperEx(TlaBoolOper.not, NameEx("x")),
          OperEx(TlaBoolOper.not, NameEx("y")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG2: ~(x /\ y) ~~> ~x \/ ~y""") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.and, NameEx("x"), NameEx("y")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.or,
          OperEx(TlaBoolOper.not, NameEx("x")),
          OperEx(TlaBoolOper.not, NameEx("y")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-NEG3: ~(x => y) ~~> x /\\ ~y") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.implies, NameEx("x"), NameEx("y")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.and,
          NameEx("x"),
          OperEx(TlaBoolOper.not, NameEx("y")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-NEG4: ~(x <=> y) ~~> ~x <=> y") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.equiv, NameEx("x"), NameEx("y")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected =
          OperEx(TlaBoolOper.equiv,
            OperEx(TlaBoolOper.not, NameEx("x")), NameEx("y"))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-NEG5: ~~x ~~> x") {
    val ex = OperEx(TlaBoolOper.not, OperEx(TlaBoolOper.not, NameEx("x")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx("x") == nextState.ex)
        assert(state.arena == nextState.arena)
        assert(state.binding == nextState.binding)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG6: ~\E x \in S: p ~~> \A x \in S: ~p""") {
    val ex = OperEx(TlaBoolOper.not,
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("S"), NameEx("p")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.forall, NameEx("x"), NameEx("S"),
          OperEx(TlaBoolOper.not, NameEx("p")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)
        assert(state.binding == nextState.binding)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG7: ~\A x \in S: p ~~> \E x \in S: ~p""") {
    val ex = OperEx(TlaBoolOper.not,
      OperEx(TlaBoolOper.forall, NameEx("x"), NameEx("S"), NameEx("p")))
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("S"),
          OperEx(TlaBoolOper.not, NameEx("p")))
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)
        assert(state.binding == nextState.binding)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG9: ~c_i ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell

    val ex = OperEx(TlaBoolOper.not, cell.toNameEx)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, cell.toNameEx, arena.cellFalse().toNameEx))
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            assert(solverContext.sat())
            rewriter.pop()
            solverContext.assertGroundExpr(OperEx(TlaBoolOper.not, nextState.ex))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG9: ~x ~~> c_TRUE""") {
    val ex = OperEx(TlaBoolOper.not, NameEx("x"))
    val binding = new Binding() + ("x" -> arena.cellFalse())
    val state = new SymbState(ex, CellTheory(), arena, binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(arena.cellTrue().toString == name)

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND1: FALSE /\ TRUE ~~> $B$0""") {
    val ex = OperEx(TlaBoolOper.and, ValEx(TlaFalse), ValEx(TlaTrue))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(solverContext.falseConst) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND4: c_1 /\ c_2 ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val c1 = arena.topCell
    arena = arena.appendCell(BoolT())
    val c2 = arena.topCell

    val ex = OperEx(TlaBoolOper.and, c1.toNameEx, c2.toNameEx)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            assert(solverContext.sat())
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, c1.toNameEx, arena.cellFalse().toNameEx))
            assert(!solverContext.sat())
            rewriter.pop()
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, c1.toNameEx, arena.cellTrue().toNameEx))
            assert(solverContext.sat())
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, c2.toNameEx, arena.cellTrue().toNameEx))
            assert(solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR4: empty \/ ~~> $B$0""") {
    val ex = OperEx(TlaBoolOper.or)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(solverContext.falseConst) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND4: empty /\ ~~> $B$1""") {
    val ex = OperEx(TlaBoolOper.and)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(solverContext.trueConst) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR1: FALSE \/ TRUE ~~> $B$1""") {
    val ex = OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    new SymbStateRewriter(solverContext).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(NameEx(solverContext.trueConst) == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR5: c_1 \/ c_2 ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell

    val ex = OperEx(TlaBoolOper.or, left.toNameEx, right.toNameEx)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(BoolTheory().hasConst(name))
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, left.toNameEx, arena.cellFalse().toNameEx))
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            assert(solverContext.sat())
            solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellFalse().toNameEx))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NE1: $B$1 != $B$2 ~~> $B$3""") {
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell

    val ex = OperEx(TlaOper.ne, left.toNameEx, right.toNameEx)
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        solverContext.assertGroundExpr(predEx)
        rewriter.push()
        // both false
        assert(solverContext.sat())
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, left.toNameEx, arena.cellFalse().toNameEx))
        assert(solverContext.sat())
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellFalse().toNameEx))
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellTrue().toNameEx))
        assert(solverContext.sat())
        rewriter.pop()
        // both true
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, left.toNameEx, arena.cellTrue().toNameEx))
        assert(solverContext.sat())
        rewriter.push()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellTrue().toNameEx))
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(OperEx(TlaOper.eq, right.toNameEx, arena.cellFalse().toNameEx))
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-EX2: \E x \in {}: TRUE ~~> FALSE""") {
    val ex = tla.exists(tla.name("x"), tla.enumSet(), tla.bool(true))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val nextState = new SymbStateRewriter(solverContext).rewriteUntilDone(state)
    assert(NameEx(solverContext.falseConst) == nextState.ex)
  }

  test("""SE-EX3: \E x \in {1, 2, 3}: x = 2 ~~> $B$k""") {
    val ex = tla.exists(tla.name("x"),
      tla.enumSet(tla.int(1), tla.int(2), tla.int(3)),
      tla.eql(tla.int(2), tla.name("x")))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(rewriter, nextState)
  }

  test("""SE-EX3: \E x \in {1, 2, 3}: x > 4 ~~> $B$k""") {
    val ex = tla.exists(tla.name("x"),
      tla.enumSet(tla.int(1), tla.int(2), tla.int(3)),
      tla.gt(tla.name("x"), tla.int(4)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain(rewriter, nextState)
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(solverContext.sat())
  }

  test("""SE-ALL3: \A x \in {1, 2, 3}: x < 10 ~~> $B$k""") {
    val ex = tla.forall(tla.name("x"),
      tla.enumSet(tla.int(1), tla.int(2), tla.int(3)),
      tla.lt(tla.name("x"), tla.int(10)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(rewriter, nextState)
  }

  test("""SE-ALL3: \A x \in {1, 2, 3}: x > 2 ~~> $B$k""") {
    val ex = tla.forall(tla.name("x"),
      tla.enumSet(tla.int(1), tla.int(2), tla.int(3)),
      tla.gt(tla.name("x"), tla.int(2)))
    val state = new SymbState(ex, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain(rewriter, nextState)
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(solverContext.sat())
  }
}
