package at.forsyte.apalache.tla.bmcmt

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir.convenience.tla
import org.scalatest.{BeforeAndAfter, FunSuite}

class RewriterBase extends FunSuite with BeforeAndAfter {
  protected var solverContext: SolverContext = new PreproSolverContext(new Z3SolverContext())
  protected var arena: Arena = Arena.create(solverContext)

  before {
    solverContext = new PreproSolverContext(new Z3SolverContext(debug = true))
    arena = Arena.create(solverContext)
  }

  after {
    solverContext.dispose()
  }

  protected def create(): SymbStateRewriterAuto = {
    new SymbStateRewriterAuto(solverContext)
  }

  protected def createWithoutCache(): SymbStateRewriter = {
    new SymbStateRewriterImpl(solverContext)
  }

  protected def assertUnsatOrExplain(rewriter: SymbStateRewriter, state: SymbState): Unit = {
    assertOrExplain("UNSAT", rewriter, state, !solverContext.sat())
  }

  protected def assumeTlaEx(rewriter: SymbStateRewriter, state: SymbState): SymbState = {
    val nextState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()))
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    nextState
  }

  protected def assertTlaExAndRestore(rewriter: SymbStateRewriter, state: SymbState): Unit = {
    rewriter.push()
    val nextState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()))
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(rewriter, nextState)
    rewriter.pop()
    rewriter.pop()
  }

  private def assertOrExplain(msg: String, rewriter: SymbStateRewriter,
                              state: SymbState, outcome: Boolean): Unit = {
    if (!outcome) {
      val writer = new StringWriter()
      new SymbStateDecoder(solverContext, rewriter).dumpArena(state, new PrintWriter(writer))
      solverContext.log(writer.getBuffer.toString)
      solverContext.push() // push and pop flush the log output
      solverContext.pop()
      fail("Expected %s, check log.smt for explanation".format(msg))
    }

  }
}
