package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions._
import at.forsyte.apalache.tla.lir.control.{LetInOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.db.{BodyDB, SourceDB}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.plugins.Identifier
import com.google.inject.Singleton

/**
  * Object responsible for pre-processing input before it is passed to the
  * [[at.forsyte.apalache.tla.assignments.AssignmentStrategyEncoder encoder]].
  */
@Singleton
class Transformer {
  // Igor: this class does a lot of things. Write comments on what the outcome is.
  // Igor: Does this class have to be stateful?
  //
  // Igor: Let's find a better name for this class.
  //
  // Igor @ 27/12/2017: converted from a singleton to a class.
  // Let Guice take care of instantiating the object rightly.

  /**
    * Extracts information about operators' bodies and stores it for later substitution.
    *
    * @param p_decls  Collection of declarations. All instances that are not [[TlaOperDecl]] are ignored.
    * @param p_bodyDB Mapping from operator names to their bodies.
    */
  def extract( p_decls : TlaDecl*
             )
             ( implicit p_bodyDB : BodyDB
             ) : Unit = {

    p_decls.foreach( OperatorHandler.extract( _, p_bodyDB ) )
  }

  /**
    * Extracts variable declarations.
    *
    * @param p_decls Collection of declarations. All instances that are not [[TlaVarDecl]] are ignored.
    * @return A set of variable names.
    */
  def getVars( p_decls : TlaDecl* ) : Set[String] = {
    p_decls.withFilter( _.isInstanceOf[TlaVarDecl] ).map( _.name ).toSet
  }

  /**
    * Replaces all occurrences of operator application with their bodies until a fixpoint is reached.
    *
    * Occurrences of [[TlaRecOperDecl]] are not expanded.
    *
    * @param p_expr   Input expression.
    * @param p_bodyDB Mapping from operator names to their bodies. Should not contain recursive operators.
    * @param p_srcDB  Mapping from replaced expressions to their originals.
    * @return A new [[TlaEx]], where all operator applications, for operators from `p_bodyDB`, have been
    *         replaced by their bodies (with parameters substituted by the arguments).
    */
  def inlineAll(
                 p_expr : TlaEx
               )
               (
                 implicit p_bodyDB : BodyDB,
                 p_srcDB : SourceDB
               ) : TlaEx = {

    OperatorHandler.unfoldMax( p_expr, p_bodyDB, p_srcDB )
  }

  /**
    * Recursively replaces UNCHANGED (x1,...,xn) by x1' \in {x1} /\ ... /\ xn' \in {xn}
    *
    * @param p_ex  Input expression.
    * @param srcDB Mapping from replaced expressions to their originals.
    * @return A new [[TlaEx]], where all occurrences of UNCHANGED have been replaced
    *         by their equivalent alpha-TLA+ compatible forms.
    */
  def unchangedExplicit(
                         p_ex : TlaEx
                       )(
                         implicit srcDB : SourceDB
                       ) : TlaEx = {

    def exFun( ex : TlaEx ) : TlaEx = {
      /** Make x' \in {x} expression */
      def lambda( x : TlaEx ) =
        Builder.in( Builder.prime( x ), Builder.enumSet( x ) )


      val ret = ex match {
        case OperEx( TlaActionOper.unchanged, arg ) =>

          /** Consider UNCHANGED x
            * and UNCHANGED (x,y,...)
            * */
          arg match {
            case OperEx( TlaFunOper.tuple, args@_* ) =>
              Builder.and( args.map( lambda ) : _* )
            case NameEx( _ ) => lambda( arg )
            case _ => ex
          }
        case _ => ex
      }

      /** Identify at the end */
      Identifier.identify( ret )
      ret
    }

    OperatorHandler.replaceWithRule( p_ex, exFun, srcDB )
  }


  def isRecursive( d : TlaOperDecl ) : Boolean =
    RecursiveProcessor.computeFromTlaEx[Boolean](
      RecursiveProcessor.DefaultFunctions.naturalTermination,
      _ == NameEx( d.name ),
      _ == NameEx( d.name ),
      RecursiveProcessor.DefaultFunctions.childCollect[TlaEx, Boolean](
        false,
        _ || _
      )
    )( d.body )


  /**
    * Jure, 15.10.2018: DOES NOT WORK WITH NESTED LET-INs !!!
    * */
  /**
    * Substitutes applications of operators declared in a LET-IN statement by their bodies.
    *
    * Undefined behaviour on recursive operators.
    *
    * @see inlineAll
    * @param p_ex Input expression
    * @param srcDB Mapping from replaced expressions to their originals.
    * @return A new [[TlaEx]], where all occurrences of operator applications,
    *         for operators declared in a LET expression,
    *         have been replaced by their bodies (with parameters substituted by arguments).
    */
  def explicitLetIn(
                     p_ex : TlaEx
                   )(
                     implicit srcDB : SourceDB
                   ) : TlaEx = {
    def exFun( ex : TlaEx ) : TlaEx = {
      ex match {
        case OperEx( oper : LetInOper, body ) =>
          /** Make a fresh temporary DB, store all decls inside */
          val bodyDB = new BodyDB()
          oper.defs.foreach( OperatorHandler.extract( _, bodyDB ) )

          /** inline as if operators were external */
          explicitLetIn( inlineAll( body )( bodyDB, srcDB ) )( srcDB )
        case _ => ex
      }
    }

    OperatorHandler.replaceWithRule( p_ex, exFun, srcDB )
  }

  /**
    * Recursively replaces x' = y by x' \in {y}
    *
    * @param p_ex  Input expression.
    * @param srcDB Mapping from replaced expressions to their originals.
    * @return A new [[TlaEx]], where all occurrences of x' = y have been replaced
    *         by x' \in {y}.
    */
  def rewriteEQ(
                 p_ex : TlaEx
               )
               (
                 implicit srcDB : SourceDB
               ) : TlaEx = {
    def lambda( tlaEx : TlaEx ) : TlaEx = {
      tlaEx match {
        case OperEx( TlaOper.eq, lhs@OperEx( TlaActionOper.prime, _ ), rhs ) =>
          OperEx( TlaSetOper.in, lhs, OperEx( TlaSetOper.enumSet, rhs ) )
        case e@_ => e
      }
    }

    OperatorHandler.replaceWithRule( p_ex, lambda, srcDB )
  }

  //
  // TODO : develop flags for sanitize, to know which transformations to perform
  //

  /**
    * Performs several transformations in sequence.
    *
    * Currently, performs the following:
    *   1. [[inlineAll]]
    *   1. [[rewriteEQ]]
    *   1. [[unchangedExplicit]]
    * @param p_expr Input expression.
    * @param bodyDB Operator body mapping, for unfolding.
    * @param srcDB Mapping from replaced expressions to their originals.
    * @return Expression obtained after applying the sequence of transformations.
    */
  def sanitize(
                p_expr : TlaEx
              )
              (
                implicit bodyDB : BodyDB,
                srcDB : SourceDB
              ) : TlaEx = {
    val inlined = inlineAll( p_expr )( bodyDB, srcDB )


    val eqReplaced = rewriteEQ( inlined )(srcDB )

    /* val ucReplaced = */ unchangedExplicit( eqReplaced )( srcDB )

  }

  // Igor: normally, the most important methods come first in a class declaration.
  // Igor: why is this method declared with apply? What is special about it?
  /**
    * Performs [[extract]], followed by [[sanitize]] and identification.
    * @param p_expr Input expression.
    * @param p_decls Collection of declared operators.
    * @param p_bodyDB Mapping from operator names to their bodies. Should not contain recursive operators.
    * @param p_srcDB  Mapping from replaced expressions to their originals.
    * @return None, if [[sanitize]] fails, otherwise contains the sanitized expression.
    */
  def apply( p_expr : TlaEx,
             p_decls : TlaDecl*
           )(
             implicit p_bodyDB : BodyDB,
             p_srcDB : SourceDB
           ) : Option[TlaEx] = {
    Identifier.identify( p_expr )
    p_decls.foreach( Identifier.identify )
    extract( p_decls : _* )( p_bodyDB )
    val san = sanitize( p_expr )( p_bodyDB, p_srcDB )
    if ( san.isNull ) None
    else {
      Identifier.identify( san )
      Some( san )
    }
  }

}
