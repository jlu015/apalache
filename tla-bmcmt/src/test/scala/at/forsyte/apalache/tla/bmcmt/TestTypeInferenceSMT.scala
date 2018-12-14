package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.assignments.{AssignmentException, Transformer}
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.bmcmt.types.{ConcreteInterfaceZ3, Eql, SmtInternal, StrConst}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.bmcmt.types.NamesAndTypedefs._
import at.forsyte.apalache.tla.imp._
import at.forsyte.apalache.tla.lir.db.{BodyDB, DummySrcDB, SourceDB}
import at.forsyte.apalache.tla.lir.oper.FixedArity
import at.forsyte.apalache.tla.lir.plugins.UniqueDB
import types._

import scala.collection.immutable.SortedMap
import scalaz.State._
import scalaz.Scalaz._

@RunWith( classOf[JUnitRunner] )
class TestTypeInferenceSMT extends FunSuite with TestingPredefs {

  val testFolderPath = "src/test/resources/"

  val z3 = ConcreteInterfaceZ3( default_soft_asserts = false )

  def testFromFile( p_file : String, p_next : String = "Next" ) : Boolean = {

    val decls = declarationsFromFile( testFolderPath + p_file )

    testFromDecls( decls, p_next )
  }

  def testFromDecls( p_decls: Seq[TlaDecl], p_next : String ) : Boolean = {
    UniqueDB.clear()
    val bodyDB = new BodyDB
    val srcDB = DummySrcDB //new SourceDB

    val declsRenamed = OperatorHandler.uniqueVarRename( p_decls )

    val transformer = new Transformer()

    /** Make all LET-IN calls explicit, to move towards alpha-TLA+ */

    val decls = declsRenamed

//    val decls = declsRenamed.map(
//      {
//        case d@TlaOperDecl( name, params, body ) =>
//          TlaOperDecl( name, params, transformer.explicitLetIn( body )( srcDB ) )
//        case e@_ => e
//      }
//    )

    /** Extract variable declarations */
    val tlaVars = transformer.getVars( decls : _* )

    /** Extract transition relation */
    val nextBody = findBodyOf( p_next, decls : _* )

    /** If extraction failed, throw */
    //    assert( !nextBody.isNull )
    if ( nextBody.isNull )
      throw new AssignmentException(
        "%s not found or not an operator".format( p_next )
      )

    /** Sanity check */
    assert( nextBody.ID.valid )
    //      throw new AssignmentException(
    //        "%s has an invalid ID".format( p_nextName )
    //      )

    /** Preprocess body (inline operators, replace UNCHANGED, turn equality to set membership, etc.) */
    val cleaned = Some(nextBody) //transformer( nextBody, decls : _* )( bodyDB, srcDB )

    /** Sanity check */
    assert( cleaned.isDefined && cleaned.get.ID.valid )
    //      throw new AssignmentException(
    //        "%s could not be sanitized".format( p_nextName )
    //      )

    val phi = cleaned.get

//    println(s"phi: ${phi}")

    val bodyName = "nextBody"

    val varMap : NameMap = (tlaVars map { s => (s,StatelessFunctions.varNameMod(s))}).toMap

    val declMap : DeclMap = (decls.filter {_.isInstanceOf[TlaOperDecl]} map {  d => d.name -> d.asInstanceOf[TlaOperDecl] }).toMap

    z3.specFramework( tlaVars.toList )(
      for {
        _ <- z3.declareConst( bodyName )
        spec <- z3.nabla( bodyName, phi, varMap, declMap )
//        _ = { println( spec.prettyPrint ) }
        _ <- z3.assertSMT( spec )
      } yield()
    ).run( SmtInternal.init() )._2

  }

  val exs : Vector[OperEx] = Vector(
    // Logic
    tla.eql( 0, 1 ),
    tla.eql( n_x, 1 ),
    tla.eql( n_x, n_y ),
    tla.eql( n_x, n_x ),

    tla.and(),
    tla.and( trueEx ),
    tla.and( trueEx, n_x ),

    tla.exists( n_b, n_S, n_p ),
    tla.forall( n_b, tla.enumSet( 1, 2, 3 ), tla.ge( n_x, n_b ) ),

    tla.choose( n_b, n_S, n_p ),
    tla.choose( n_b, tla.enumSet( 1, 2, 3 ), tla.le( n_b, 0 ) ),

    // Arith
    tla.plus( 1, 2 ),
    tla.plus( n_x, 2 ),
    tla.plus( n_x, n_y ),
    tla.plus( n_x, n_x ),
    tla.plus( n_x, tla.choose( n_b, tla.enumSet( 1, 2, 3 ), tla.le( n_b, 0 ) ) ),

    tla.dotdot( 1, 2 ),
    tla.dotdot( n_x, 2 ),
    tla.dotdot( n_x, n_y ),
    tla.dotdot( n_x, n_x ),

    tla.lt( 1, 2 ),
    tla.lt( n_x, 2 ),
    tla.lt( n_x, n_y ),
    tla.lt( n_x, n_x ),

    // Sets
    tla.in( 2, tla.enumSet( 0, 1 ) ),
    tla.in( n_x, tla.enumSet( 0, 1 ) ),
    tla.in( n_x, n_S ),

    tla.subseteq( tla.enumSet( 0 ), tla.enumSet( 0, 1 ) ),
    tla.subseteq( n_S, tla.enumSet( 0, 1 ) ),
    tla.subseteq( n_S, n_T ),
    tla.subseteq( n_S, n_S ),

    tla.cap( tla.enumSet( 0, 1 ), tla.enumSet( 1, 2 ) ),
    tla.cap( n_S, tla.enumSet( 1, 2 ) ),
    tla.cap( n_S, n_T ),
    tla.cap( n_S, n_S ),

    tla.enumSet(),
    tla.enumSet( 0 ),
    tla.enumSet( 0, 1 ),
    tla.enumSet( 0, n_x ),
    tla.enumSet( n_x, n_y ),
    tla.enumSet( n_x, n_x ),

    tla.filter( n_b, tla.enumSet( 0, 1, 2 ), tla.ge( n_b, n_x ) ),
    tla.filter( n_b, n_S, n_p ),

    tla.map( tla.ge( n_b, n_x ), n_b, tla.enumSet( 0, 1, 2 ) ),
    tla.map( n_e, n_b, n_S ),
    tla.map( 0, n_x, n_S, n_y, n_T, n_z, n_Q),

    tla.powSet( tla.enumSet() ),
    tla.powSet( tla.enumSet( 0 ) ),
    tla.powSet( tla.enumSet( 0, 1 ) ),
    tla.powSet( tla.enumSet( 0, n_x ) ),
    tla.powSet( tla.enumSet( n_x, n_y ) ),
    tla.powSet( n_S ),

    tla.union( tla.enumSet() ),
    tla.union( tla.enumSet( tla.enumSet( 0 ) ) ),
    tla.union( tla.enumSet( tla.enumSet( 0 ), tla.enumSet( 1 ) ) ),
    tla.union( tla.enumSet( tla.enumSet( 0 ), n_x, tla.enumSet( 1, 2, 3 ) ) ),
    tla.union( tla.enumSet( n_x, n_y ) ),
    tla.union( n_S ),

    // Fun
    tla.dom( tla.funDef(0, n_x, n_S) ),
    tla.dom( tla.funDef(tla.plus(n_x, n_y), n_x, n_S, n_y, n_T) ),
    tla.dom( n_f ),

    tla.funDef( tla.appFun( n_f, n_x), n_x, tla.enumSet( 0, 3, -3 ) ),
    tla.funDef( n_e, n_x, n_S ),
    tla.funDef( n_e, n_x, n_S, n_y, n_T ),
    tla.funDef( n_e, n_x, n_S, n_y, n_S ),

    tla.funSet( tla.enumSet(), tla.enumSet() ),
    tla.funSet( tla.enumSet(), tla.enumSet(1, 2) ),
    tla.funSet( tla.enumSet(1,2), tla.enumSet(1, 2) ),
    tla.funSet( tla.enumSet(1,2), n_T ),
    tla.funSet( tla.enumSet(1,n_x), n_T ),
    tla.funSet( n_S, n_T ),

    // overloaded

    // Records
    tla.enumFun( tla.str( "a" ), 1 ),
    tla.enumFun( tla.str( "a" ), 1, tla.str( "b" ), tla.str( "b" ) ),
    tla.enumFun( tla.str( "a" ), n_x, tla.str( "b" ), n_y ),
    tla.enumFun( tla.str( "a" ), n_x, tla.str( "b" ), n_x ),

    tla.recSet( tla.str( "a" ), tla.enumSet(), tla.str( "b" ), n_T ),
    tla.recSet( tla.str( "a" ), tla.enumSet(1,2), tla.str( "b" ), n_T ),
    tla.recSet( tla.str( "a" ), n_S, tla.str( "b" ), n_T ),

    // Tuples
    tla.tuple(),
    tla.tuple(1, 2),
    tla.tuple(1, n_x),
    tla.tuple(n_x, n_y, 2, n_z),
    tla.tuple(n_x, n_x, n_x, n_x),

    tla.times(),
    tla.times(tla.enumSet()),
    tla.times(tla.enumSet(1,2)),
    tla.times(tla.enumSet(), tla.enumSet(1,2)),
    tla.times(tla.enumSet(1,2), tla.enumSet(1,2)),
    tla.times(tla.enumSet(1,2), n_T),
    tla.times(n_S, n_T, n_Q),

    // Sequences
    tla.concat( tla.tuple(), tla.tuple() ),
    tla.concat( tla.tuple(1,2), tla.tuple(3,4) ),
    tla.concat( n_x, n_y ),

    tla.head( tla.tuple() ),
    tla.head( tla.tuple(1,2,3) ),
    tla.head( n_x ),

    tla.tail( tla.tuple() ),
    tla.tail( tla.tuple(1,2,3) ),
    tla.tail( n_x ),

    tla.len( tla.tuple() ),
    tla.len( tla.tuple(1,2,3) ),
    tla.len( n_x ),

    tla.seqSet( tla.enumSet() ),
    tla.seqSet( tla.enumSet(1,2,3) ),
    tla.seqSet( n_S ),

    tla.append( tla.tuple(), 0 ),
    tla.append( tla.tuple(3,2,1), 0 ),
    tla.append( n_x, n_e ),

    // Control
    tla.ite( trueEx, 0, 1),
    tla.ite( n_p, n_x, n_y),

    tla.caseSplit( trueEx, 0 ),
    tla.caseSplit( trueEx, 0, falseEx, 1 ),
    tla.caseSplit( n_p, n_x, n_q, n_y, n_r, n_z ),

    tla.caseOther( 1, trueEx, 0 ),
    tla.caseOther( 2, trueEx, 0, falseEx, 1 ),
    tla.caseOther( n_e, n_p, n_x, n_q, n_y, n_r, n_z ),

    // except, rec or fun
    tla.except( n_f, tla.tuple( tla.str( "a" ) ), 1, tla.tuple( tla.str( "b" ) ), tla.str( "b" ) ),
    tla.dom( tla.except( n_f, tla.tuple( tla.str( "a" ) ), 1, tla.tuple( tla.str( "b" ) ), 2 ) ),

    // app, record or fun
    tla.and( tla.eql( tla.appFun( n_f, tla.str( "a" ) ), 1 ), tla.eql( tla.appFun( n_f, tla.str( "b" ) ), 2 ) ),
    tla.and( tla.eql( tla.appFun( n_f, tla.str( "a" ) ), 1 ), tla.eql( tla.appFun( n_f, tla.str( "b" ) ), tla.str( "b" ) ) ),

    // app, tuple or seq
    tla.and( tla.eql( tla.appFun( n_f, 1 ), tla.str( "a" ) ), tla.eql( tla.appFun( n_f, 2 ), 2 ) ),
    tla.and( tla.eql( tla.appFun( n_f, 1 ), 1 ), tla.eql( tla.head( n_f ), 42 ) )
  )

  val failExs : Vector[OperEx] = Vector(
    tla.eql( 0, tla.str( "a" ) ),
    tla.and( trueEx, 1 ),
    tla.exists( n_x, 1, n_p ),
    tla.choose( n_x, tla.enumSet( tla.str( "a" ), tla.str( "b" ) ), tla.ge( n_x, 0 ) ),
    tla.in( n_S, n_S )
  )

  val vars = List(
    "x", "y", "z", "S", "T", "Q", "f", "p", "q", "r", "e"
  )

  val varMap : NameMap = (vars map { s => (s,StatelessFunctions.varNameMod(s))}).toMap

  ignore( "Basic SMT" ) {
    val cmp = for {
      _ <- z3.declareDatatypes()
      _ <- z3.declareConst("A")
      _ <- z3.declareConst("B")
      _ <- z3.assertSMT( Eql( StrConst("A"), StrConst("B") ) )
      _ <- z3.assertSMT( Eql( StrConst("A"), StrConst("intT") ) )
//      _ <- closing() // NOTE: z3 implementation doesn't seem to want this in the parsed spec.
      sat <- z3.isSat
    } yield sat

    val (_,sat) = cmp.run(SmtInternal.init())
//    val spec = int.partialSpec

//    println(s"SAT: ${sat}")
//    println(spec)
    assert(sat)

  }

  ignore("Functions and Axioms") {
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

    val (int,sat) = cmp.run(SmtInternal.init())
    val spec = int.partialSpec


    println(s"SAT: ${sat}")
    println(spec)
    assert(sat)
  }

  ignore("Delta") {
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

  ignore( "templateFromOper" ) {
    val templates = exs map z3.templateFromOper

    val formulas = exs.indices map { i =>
      val t = templates(i)( "e", exs(i).args.indices.toList  map { i => s"t_${i}" } )

      val (_,ex) = t.run( SmtInternal.init() )
      s"${exs(i)} ~template~> $ex"
    }

   formulas foreach {f => println(s"$f\n") }

  }

  test( "Nabla: Builtin" ){

    val bodyName = "b"

    def cmpNablas( v: Vector[OperEx] ) : List[Boolean] = v.toList map { phi =>
      z3.specFramework( vars )(
        for {
          _ <- z3.declareConst( bodyName )
          spec <- z3.nabla( bodyName, phi, varMap, Map.empty )
          _ <- z3.assertSMT( spec )
        } yield()
      )
    } map {
      _.run( SmtInternal.init() )._2
    }

    val vec = exs
    val fvec = failExs

    val nablas = cmpNablas( vec )
    val mustFail = cmpNablas( fvec )

    val fails = nablas.zipWithIndex filterNot { case(b, i) => b } map { _._2 }
    val failFails = mustFail.zipWithIndex filter { case(b, i) => b } map { _._2 }

    if (fails.nonEmpty) {
      println( "Fails on SAT:" )
      fails foreach { i => println( s"$i => ${vec( i )}" ) }
    }
    if( failFails.nonEmpty ) {
      println( "Fails on UNSAT:" )
      failFails foreach { i => println( s"$i => ${fvec( i )}" ) }
    }

    assert( fails.isEmpty && failFails.isEmpty )

  }

  test( "Nabla: UserOps" ) {
    val declA = tla.declOp( "A", 42 )
    val declB = tla.declOp( "B", n_x, SimpleFormalParam("x") )
    val declC = tla.declOp( "C", tla.plus( n_x, n_y ) , SimpleFormalParam("x") )
    val declD = tla.declOp( "D", tla.appDecl( declB, 0 ) )
    val declE = tla.declOp( "E", n_p, OperFormalParam( "Q", FixedArity( 1 ) ), SimpleFormalParam( "p" ) )
    val declF = tla.declOp( "F", tla.appOp( n_Q, n_p ), OperFormalParam( "Q", FixedArity( 1 ) ), SimpleFormalParam( "p" ) )
    val declG = tla.declOp( "G", tla.appDecl( declF, "C", 1 ) )

    val declRM = tla.declOp("RM", tla.enumSet( 1,2,3,4 ) )
    val declPrepare = tla.declOp(
      "Prepare",
      tla.and(
        tla.eql( tla.appFun( n_f, n_p ), tla.str( "a" ) ),
        tla.primeEq(
          n_f,
          tla.except(
            n_f,
            tla.tuple( n_p ),
            tla.str( "b" )
          )
        )
      ),
      SimpleFormalParam( "p" ) )

    val declEPrepare = tla.declOp( "Next", tla.exists( n_t, tla.appDecl( declRM ) , tla.appDecl( declPrepare, n_t)))

    val decls : Vector[TlaOperDecl] = Vector(
      declA,
      declB,
      declC,
      declD,
      declE,
      declF,
      declG,
      declRM,
      declPrepare,
      declEPrepare
    )

    val declMap : DeclMap = (decls map {  d => d.name -> d }).toMap

    val bodyName = "e"

    def displayParam(p: FormalParam) : String = p match {
      case SimpleFormalParam(x) => x
      case OperFormalParam(x, FixedArity(n)) if n > 0 => s"$x(${List.fill(n)("_") mkString ", "})"
      case OperFormalParam(x, _) => s"$x(?)"
    }

    def nTs(n: Int) : List[String] = Range(0,n).toList map { i=> s"t_$i"}

    def cmpTemplates( v: Vector[TlaOperDecl] ) : List[Boolean] = v.toList map { decl =>
      val ts : List[String] = nTs( decl.formalParams.size )
      z3.specFramework( vars )(
        for {
          _ <- z3.declareConst( bodyName )
          _ <- ts traverseS {z3.declareConst(_)}
          expr <- z3.templateFromDecl( decl, varMap, declMap )( bodyName, ts )
//          _ = { println( s"${decl.name}(${ decl.formalParams map displayParam mkString ", " }) = ${decl.body} -> template_${decl.name}(${ bodyName +: ts mkString ", " }) := ${expr.prettyPrint}" ) }
          _ <- z3.assertSMT( expr )
        } yield()
      )
    } map {
      _.run( SmtInternal.init() )._2
    }

    val results = cmpTemplates( decls )
    val fails = results.zipWithIndex filterNot { case(b, i) => b } map { _._2 }

    if (fails.nonEmpty) {
      println( "Fails on SAT:" )
      fails foreach { i => println( s"$i => ${decls( i )}" ) }
    }
    assert( fails.isEmpty )


  }

  ignore( "Spec from file: test1 " ) {
    val sat = testFromFile( "test1.tla" )
    assert(sat)
  }
  ignore( "Spec from file: test2 " ) {
    val sat = testFromFile( "test2.tla" )
    assert(sat)
  }
  test( "Spec from file: TCommit " ) {
    val sat = testFromFile( "TCommit.tla", "TCNext" )
    assert(sat)
  }

  test( "Spec from file: RNC " ) {
    testFromFile( "raft_no_constants.tla" )
  }

}
