package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.{SimpleFormalParam, TestingPredefs}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.bmcmt.types.{ConcreteInterfaceZ3, Eql, SmtInternal, StrConst}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.bmcmt.types.NamesAndTypedefs._
import types._

import scala.collection.immutable.SortedMap
import scalaz.State._

@RunWith( classOf[JUnitRunner] )
class TestTypeInferenceSMT extends FunSuite with TestingPredefs {
  ignore( "Basic SMT" ) {

    val z3 = ConcreteInterfaceZ3( default_soft_asserts = false )

    val cmp = for {
      _ <- z3.declareDatatypes()
      _ <- z3.declareConst("A")
      _ <- z3.declareConst("B")
      _ <- z3.assertSMT( Eql( StrConst("A"), StrConst("B") ) )
      _ <- z3.assertSMT( Eql( StrConst("A"), StrConst("intT") ) )
//      _ <- closing() // NOTE: z3 implementation doesn't seem to want this in the parsed spec.
      sat <- z3.isSat
    } yield sat

    val (SmtInternal(spec,_,_,_),sat) = cmp.run(SmtInternal.init())

    println(s"SAT: ${sat}")
    println(spec)
    assert(sat)

  }

  ignore("Functions and Axioms") {

    val z3 = ConcreteInterfaceZ3( default_soft_asserts = false )

    val cmp = for {
      _ <- z3.declareDatatypes()
      _ <- z3.addFunctions()
      _ <- z3.addAxioms()
      _ <- z3.addTlaVariableConstants( List("A", "B") )
      _ <- z3.assertSMT( Eql( StrConst("var_A"), StrConst("var_B") ) )
      _ <- z3.assertSMT( Eql( StrConst("var_A"), StrConst("intT") ) )
      //      _ <- closing() // NOTE: z3 implementation doesn't seem to want this in the parsed spec.
      sat <- z3.isSat
    } yield sat

    val (SmtInternal(spec,_,_,_),sat) = cmp.run(SmtInternal.init())

    println(s"SAT: ${sat}")
    println(spec)
    assert(sat)
  }

  test("Delta") {
    import StatelessFunctions._

    val alphas = Range(0,5).toVector map alphaT

    val alphamap : TypeMap = ( alphas map { a => a -> StrConst( varNameMod( a.i.toString ) ) } ).toMap

    val ts  = Vector(
      intT,
      boolT,
      strT,
      alphas(0),
      setT( intT),
      tupT( List(intT, intT, setT(alphas(1))) ),
      recT( SortedMap( "a" -> intT, "b" -> tupT( List(intT, intT) ) ) )
    )

    val deltas = ts map { StatelessFunctions.delta( "x", _, alphamap ) }

//    deltas foreach println

    println(deltas(6))

  }

  ignore("Operators: +") {

    val z3 = ConcreteInterfaceZ3( default_soft_asserts = false )

    val variables : List[String] = List("x")
    val ex = tla.plus( "x", 2 )

    val cmp = for {
      _ <- z3.declareDatatypes()
      _ <- z3.addFunctions()
      _ <- z3.addAxioms()
      _ <- z3.addTlaVariableConstants( variables )
      _ <- z3.declareConst("qq")
      _ <- z3.declareConst("qq_0")
      _ <- z3.declareConst("qq_1")
//      _ <- z3.constraintFromSig( ex )
      //      _ <- closing() // NOTE: z3 implementation doesn't seem to want this in the parsed spec.
      sat <- z3.isSat
    } yield sat

    val (SmtInternal(spec,_,_,_),sat) = cmp.run(SmtInternal.init())

    println(s"SAT: ${sat}")
//    println(spec)
    assert(sat)
  }

  ignore("Operators: U") {

    val z3 = ConcreteInterfaceZ3( default_soft_asserts = false )

    val variables : List[String] = List("x")
    val ex = tla.cup( "x", "x" )

    val cmp = for {
      _ <- z3.declareConst("qq")
      _ <- z3.declareConst("qq_0")
      _ <- z3.declareConst("qq_1")
//      _ <- z3.constraintFromSig( ex )
    } yield ()

    val fw = z3.specFramework( variables )(cmp)

    val (SmtInternal(spec,_,_,_),sat) = fw.run(SmtInternal.init())

    println(s"SAT: ${sat}")
    //    println(spec)
    assert(sat)
  }

//  test("Operators: User defined"){
//    val z3 = ConcreteInterfaceZ3( default_soft_asserts = false )
//
//    val variables : List[String] = List("x")
//
//    val decl = tla.declOp( "X", tla.plus( n_y, 1 ), SimpleFormalParam( "y" ) ) // X(y) = y + 1
//
//    val cmp = z3.toplevelOperatorSpec( decl )
//
//    val fw = z3.specFramework( variables )( cmp )
//
//    val (SmtInternal(spec,_,_,_),sat) = fw.run(SmtInternal.init())
//
//    println(s"SAT: ${sat}")
//    //    println(spec)
//    assert(sat)
//  }

}
