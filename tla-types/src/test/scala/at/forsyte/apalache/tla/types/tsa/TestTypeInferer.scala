package at.forsyte.apalache.tla.types.tsa

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.plugins.Identifier
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, UID}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.mutable


@RunWith(classOf[JUnitRunner])
class TestTypeInferer extends FunSuite {
  class Fixture {
    val typeMap = mutable.Map[UID, CellT]()
    val infer = new TypeInferer(typeMap)
  }


  test("infer integer constant") {
    inferCompareNoWarn(IntT(), tla.int(1981))
  }

  test("infer boolean constant") {
    inferCompareNoWarn(BoolT(), tla.bool(false))
  }

  test("infer string constant") {
    inferCompareNoWarn(ConstT(), tla.str("foo"))
  }

  test("infer FinSetT(IntT)") {
    val args = Seq(tla.int(1), tla.int(2), tla.int(3))
    inferCompareNoWarn(FinSetT(IntT()), tla.enumSet(args: _*))
    inferCompareNoWarn(FinSetT(IntT()), tla.cap(tla.int(2), tla.int(3)))
    inferCompareNoWarn(FinSetT(IntT()), tla.cup(tla.int(2), tla.int(3)))
    inferCompareNoWarn(FinSetT(IntT()), tla.setminus(tla.int(2), tla.int(3)))
  }

  test("non-uniform sets") {
    val args = Seq(tla.int(1), tla.bool(true))
    val ex = tla.enumSet(args: _*)
    val fx = inferAndReturn(ex)
    assert("Failed to unify types Int, Bool" == fx.infer.errors.head.message)
    fx.typeMap(ex.ID) match {
      case FinSetT(UnknownT(_)) => () // OK
      case _ => fail()
    }
  }

  test("infer UNION {{1,2}, {3, 4}}") {
    val set1 = tla.enumSet(tla.int(1), tla.int(2))
    val set2 = tla.enumSet(tla.int(3), tla.int(4))
    val union = tla.union(tla.enumSet(set1, set2))
    inferCompareNoWarn(FinSetT(IntT()), union)
  }

  test("error on UNION {{1,2}, true}") {
    val elem1 = tla.enumSet(tla.int(1), tla.int(2))
    val elem2 = tla.enumSet(tla.bool(true))
    val union = tla.union(tla.enumSet(elem1, elem2))
    val fx = inferAndReturn(union)
    assert("Failed to unify types FinSet[Int], FinSet[Bool]" == fx.infer.errors.head.message)
    fx.typeMap(union.ID) match {
      case UnknownT(_) => () // OK
      case _ => fail()
    }
  }

  test("infer empty filter set") {
    val filter = tla.filter(tla.name("x"), tla.enumSet(), tla.bool(false))
    val fx = inferAndReturn(filter)
    fx.typeMap(filter.ID) match {
      case FinSetT(UnknownT(_)) => () // OK
      case _ => fail()
    }
  }

  test("infer non-empty filter set") {
    val set = tla.enumSet(tla.int(1), tla.int(2))
    inferCompareNoWarn(FinSetT(IntT()),
      tla.filter(tla.name("x"), set, tla.bool(true)))
  }

  test("infer non-empty filter set predicate") {
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val predEx = tla.bool(true)
    val fx = inferAndReturn(tla.filter(tla.name("x"), set, predEx))
    assert(BoolT() == fx.typeMap(predEx.ID))
  }

  test("error on filter") {
    val filter = tla.filter(tla.name("x"), tla.bool(true), tla.bool(true))
    val fx = inferAndReturn(filter)
    assert("Set comprehension applied to type Bool" == fx.infer.errors.head.message)
    fx.typeMap(filter.ID) match {
      case UnknownT(_) => () // OK
      case _ => fail()
    }
  }

  test("error on non-Boolean predicate") {
    val predEx = tla.int(2)
    val filter = tla.filter(tla.name("x"), tla.enumSet(tla.int(1)), predEx)
    val fx = inferAndReturn(filter)
    assert("Expected a Boolean, found Int" == fx.infer.errors.head.message)
    assert(IntT() == fx.typeMap(predEx.ID))
  }

  test("infer arithmetic") {
    inferCompareNoWarn(IntT(), tla.plus(tla.int(1), tla.int(2)))
    inferCompareNoWarn(IntT(), tla.minus(tla.int(1), tla.int(2)))
    inferCompareNoWarn(IntT(), tla.mult(tla.int(1), tla.int(2)))
    inferCompareNoWarn(IntT(), tla.div(tla.int(1), tla.int(2)))
    inferCompareNoWarn(IntT(), tla.mod(tla.int(1), tla.int(2)))
    inferCompareNoWarn(IntT(), tla.sum(tla.int(1), tla.int(2), tla.int(3)))
    inferCompareNoWarn(IntT(), tla.prod(tla.int(1), tla.int(2), tla.int(3)))
    inferCompareNoWarn(IntT(), tla.exp(tla.int(3), tla.int(4)))
    inferCompareNoWarn(FinSetT(IntT()), tla.dotdot(tla.int(1), tla.int(10)))
  }

  test("error on non-integer arithmetic") {
    inferCompareError(IntT(), tla.plus(tla.int(1), tla.bool(false)))
    inferCompareError(IntT(), tla.minus(tla.int(1), tla.bool(false)))
    inferCompareError(IntT(), tla.mult(tla.int(1), tla.bool(false)))
    inferCompareError(IntT(), tla.div(tla.int(1), tla.bool(false)))
    inferCompareError(IntT(), tla.mod(tla.int(1), tla.bool(false)))
    inferCompareError(IntT(), tla.sum(tla.int(1), tla.bool(false)))
    inferCompareError(IntT(), tla.prod(tla.int(1), tla.bool(false)))
    inferCompareError(IntT(), tla.exp(tla.int(1), tla.bool(false)))
    inferCompareError(FinSetT(IntT()), tla.dotdot(tla.int(1), tla.bool(false)))
  }

  test("infer arithmetic comparisons") {
    inferCompareNoWarn(BoolT(), tla.gt(tla.int(1), tla.int(2)))
    inferCompareNoWarn(BoolT(), tla.ge(tla.int(1), tla.int(2)))
    inferCompareNoWarn(BoolT(), tla.lt(tla.int(1), tla.int(2)))
    inferCompareNoWarn(BoolT(), tla.le(tla.int(1), tla.int(2)))
  }

  test("error on non-integer arithmetic comparisons") {
    inferCompareError(BoolT(), tla.gt(tla.int(1), tla.bool(true)))
    inferCompareError(BoolT(), tla.ge(tla.int(1), tla.bool(true)))
    inferCompareError(BoolT(), tla.lt(tla.int(1), tla.bool(true)))
    inferCompareError(BoolT(), tla.le(tla.int(1), tla.bool(true)))
  }

  test("infer finite set operators") {
    inferCompareNoWarn(BoolT(), tla.isFin(tla.enumSet(tla.int(1))))
    inferCompareNoWarn(IntT(), tla.card(tla.enumSet(tla.int(1))))
  }

  test("error on incorrect finite set arguments") {
    inferCompareError(BoolT(), tla.isFin(tla.int(1)))
    inferCompareError(IntT(), tla.card(tla.int(1)))
  }

  test("infer equalities") {
    inferCompareNoWarn(BoolT(), tla.eql(tla.int(1), tla.int(2)))
    inferCompareNoWarn(BoolT(), tla.neql(tla.int(1), tla.int(2)))
    inferCompareNoWarn(BoolT(), tla.eql(tla.bool(false), tla.bool(true)))
    inferCompareNoWarn(BoolT(), tla.neql(tla.bool(false), tla.bool(true)))
    inferCompareNoWarn(BoolT(), tla.eql(tla.str("a"), tla.str("b")))
    inferCompareNoWarn(BoolT(), tla.neql(tla.str("a"), tla.str("b")))
    inferCompareNoWarn(BoolT(),
      tla.eql(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(2))))
    inferCompareNoWarn(BoolT(),
      tla.neql(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(2))))
    // TODO: add powersets, functions, function sets, tuples, records
  }

  test("warning on constant inequalities") {
    inferCompareWarn(BoolT(), tla.eql(tla.int(1), tla.bool(false)))
    inferCompareWarn(BoolT(), tla.neql(tla.int(1), tla.bool(false)))
    inferCompareWarn(BoolT(), tla.eql(tla.str("a"), tla.bool(false)))
    inferCompareWarn(BoolT(), tla.neql(tla.str("a"), tla.bool(false)))
    inferCompareWarn(BoolT(), tla.eql(tla.str("a"), tla.int(1)))
    inferCompareWarn(BoolT(), tla.neql(tla.str("a"), tla.int(1)))
    inferCompareWarn(BoolT(), tla.eql(tla.int(1), tla.enumSet(tla.int(1))))
    inferCompareWarn(BoolT(), tla.neql(tla.int(1), tla.enumSet(tla.int(1))))
    // TODO: add powersets, functions, function sets, tuples, records
  }

  test("infer Boolean operators") {
    inferCompareNoWarn(BoolT(), tla.and(tla.bool(false), tla.bool(true)))
    inferCompareNoWarn(BoolT(), tla.or(tla.bool(false), tla.bool(true)))
    inferCompareNoWarn(BoolT(), tla.equiv(tla.bool(false), tla.bool(true)))
    inferCompareNoWarn(BoolT(), tla.impl(tla.bool(false), tla.bool(true)))
    inferCompareNoWarn(BoolT(), tla.not(tla.bool(false)))
  }

  test("infer bounded exists") {
    val set = tla.enumSet(tla.int(1))
    val pred = tla.bool(true)
    val fx = inferCompareNoWarn(BoolT(), tla.exists(tla.name("x"), set, pred))
    assert(FinSetT(IntT()) == fx.typeMap(set.ID))
    assert(BoolT() == fx.typeMap(pred.ID))
  }

  test("infer bounded forall") {
    val set = tla.enumSet(tla.int(1))
    val pred = tla.bool(true)
    val fx = inferCompareNoWarn(BoolT(), tla.forall(tla.name("x"), set, pred))
    assert(FinSetT(IntT()) == fx.typeMap(set.ID))
    assert(BoolT() == fx.typeMap(pred.ID))
  }

  test("infer unbounded exists") {
    val set = tla.enumSet(tla.int(1))
    val pred = tla.bool(true)
    val fx = inferCompareNoWarn(BoolT(),
      OperEx(TlaBoolOper.existsUnbounded, tla.name("x"), pred))
    assert(BoolT() == fx.typeMap(pred.ID))
  }

  test("infer unbounded forall") {
    val set = tla.enumSet(tla.int(1))
    val pred = tla.bool(true)
    val fx = inferCompareNoWarn(BoolT(),
      OperEx(TlaBoolOper.forallUnbounded, tla.name("x"), pred))
    assert(BoolT() == fx.typeMap(pred.ID))
  }

  private def inferAndReturn(ex: TlaEx): Fixture = {
    val fx = new Fixture()
    Identifier.identify(ex)
    fx.infer.inferRecAndStore(ex)
    fx
  }

  private def inferCompareNoWarn(expectedType: CellT, ex: TlaEx): Fixture = {
    val fx = inferAndReturn(ex)
    assert(expectedType == fx.typeMap(ex.ID))
    assert(fx.infer.errors.isEmpty, "expected no error")
    assert(fx.infer.warnings.isEmpty, "expected no warning")
    fx
  }

  private def inferCompareWarn(expectedType: CellT, ex: TlaEx): Fixture = {
    val fx = inferAndReturn(ex)
    assert(expectedType == fx.typeMap(ex.ID))
    assert(fx.infer.errors.isEmpty, "expected no warning")
    assert(fx.infer.warnings.nonEmpty, "expected a warning")
    fx
  }

  private def inferCompareError(expectedType: CellT, ex: TlaEx): Fixture = {
    val fx = inferAndReturn(ex)
    assert(expectedType == fx.typeMap(ex.ID))
    assert(fx.infer.errors.nonEmpty, "expected a warning")
    fx
  }
}
