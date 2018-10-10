package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.{TestingPredefs, TlaEx, UID}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.plugins.{Identifier, UniqueDB}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.SortedMap

@RunWith( classOf[JUnitRunner] )
class TestTypeInference extends FunSuite with TestingPredefs {

  test( "Signatures" ) {
    val exs = List(
      tla.and( n_x, n_y ),
      tla.choose( n_x, n_S, n_p ),
      tla.enumSet( seq( 10 ) : _* ),
      tla.in( n_x, n_S ),
      tla.map( n_e, n_x, n_S )
    )

    exs foreach Identifier.identify

    val sigs = exs map Signatures.get

    exs zip sigs foreach { case (x, y: Signatures.Signature) => assert( x.oper.isCorrectArity( y.args.size ) ) }
  }

  test( "Logic operators" ){
    UniqueDB.clear()

    val exs = Array(
      tla.eql( 1, 2 ),
      tla.eql( 1, n_a ),
      tla.eql( 1, tla.str( "a" ) ),
      tla.and( trueEx, falseEx, tla.eql(1, 2) ),
      tla.and( 1, 2, 3, 4 ),
      tla.enumFun( tla.str( "a"), 1, tla.str( "b" ), tla.str( "b" )  )
    )

    def run(ex: TlaEx) : TypeInference.TypeMaps = {
      Identifier.identify(ex)
      val r = TypeInference( ex )
      r
    }

    def predictExprType( ex: TlaEx, t: MinimalCellT ): Unit =
      assert( run(ex).uidMap(ex.ID) == t )
    def predictVarType( ex: TlaEx, name: String, t: MinimalCellT ): Unit =
      assert( run(ex).varTypeMap(name) == t )


//    predictExprType( exs( 0 ), BoolT() )
//    predictVarType( exs( 1 ), "a", IntT() )
//    assertThrows[TypeException]( run( exs( 2 ) ) )
//    predictExprType( exs( 3 ), BoolT() )
//    assertThrows[TypeException]( run( exs( 4 ) ) )

    predictExprType( exs(5), RecordT( SortedMap( "a" -> IntT(), "b" -> ConstT() ) ) )
  }

  ignore( "Application" ) {

    UniqueDB.clear()

    val ex = tla.eql( tla.plus(  tla.appFun( n_f, n_x ) , 2), 4 )
    val ex2 =
      tla.and(
        tla.in( n_x, n_S ),
        tla.le(
          tla.plus(
            tla.mult( 2, n_x ),
            5
          ),
          10
        ),
        tla.primeEq( n_x,
          tla.appFun(
            n_f,
            n_x
          )
        )
      )

    Identifier.identify( ex2 )

    val r = TypeInference( ex2 )

    r.uidMap foreach {
      case (k,v) => println(s"${UniqueDB.apply(k)} : $k -> $v")
    }
    UniqueDB.print()

  }
}
