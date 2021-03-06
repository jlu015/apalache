package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.control.LetInOper
import at.forsyte.apalache.tla.lir.db._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}

object EnvironmentHandlerGenerator {
  def makeDummyEH : EnvironmentHandler = new EnvironmentHandler( new UidDB, DummyBodyDB, DummySrcDB )

  def makeEH : EnvironmentHandler = new EnvironmentHandler( new UidDB, new BodyDB, new SourceDB )
}

sealed class EnvironmentHandler(
                                 val m_uidDB : UidDB,
                                 val m_bodyDB : BodyDB,
                                 val m_sourceDB : SourceDB
                               ) {
  protected[lir] object AuxFun {
    def markSrc( p_old : TlaEx,
                 p_new : TlaEx
               ) : Unit = {
      identify( p_new )
      if ( p_old.ID != p_new.ID ) {
        m_sourceDB.update( p_new.ID, p_old.ID )
      }
    }

    def pfx( p_prefix : String, p_s : String ) : String = "%s_%s".format( p_prefix, p_s )

    def renameParam( p_prefix : String )( p_param : FormalParam ) : FormalParam = p_param match {
      case SimpleFormalParam( name ) => SimpleFormalParam( pfx( p_prefix, name ) )
      case OperFormalParam( name, arity ) => OperFormalParam( pfx( p_prefix, name ), arity )
    }
  }
  def identify : TlaEx => Unit =
    RecursiveProcessor.traverseEntireTlaEx( m_uidDB.add )

  def fullyIdentified: TlaEx => Boolean = RecursiveProcessor.globalTlaExProperty( _.ID.valid )

  import AuxFun._

  /**
    * TODO: Move to transformer
    * */
  def uniqueVarRename( p_decls : Seq[TlaDecl] ) : Seq[TlaDecl] = {
    def lambda( p_boundVars : Set[String], p_prefix : String )( p_ex : TlaEx ) : TlaEx = {
      p_ex match {
        /** If we find a name, which is in our set, we prefix it */
        case NameEx( name ) =>
          if ( p_boundVars.contains( name ) ) {
            val ret = NameEx( pfx( p_prefix, name ) )
            markSrc( p_ex, ret )
            ret
          }
          else p_ex
        case OperEx( op : LetInOper, body ) =>
          val newdefs = op.defs.map(
            _ match {
              /** In the case of a LET-IN, add all bound params to the param set */
              case TlaOperDecl( name, params, declBody ) =>
                val newBody = lambda( p_boundVars ++ params.map( _.name ), p_prefix )( declBody )
                markSrc( declBody, newBody )
                TlaOperDecl(
                  name,
                  params.map( renameParam( p_prefix ) ),
                  newBody
                )
              case decl@_ => decl
            }
          )
          /** Recurse */
          val newBody = lambda( p_boundVars, p_prefix )( body )
          markSrc( body, newBody )
          val ret =
            OperEx(
              new LetInOper( newdefs ),
              newBody
            )
          markSrc( p_ex, ret )
          ret

        /** Quantifiers are a special case, since they introduce variables into the namespace */
        case OperEx( oper@(TlaBoolOper.exists | TlaBoolOper.forall), oldName@NameEx( varname ), set, body ) =>
          val newName = NameEx( pfx( p_prefix, varname ) )
          markSrc( oldName, newName )
          val newSet = lambda( p_boundVars, p_prefix )( set )
          markSrc( set, newSet )
          val newBody = lambda( p_boundVars + varname, p_prefix )( body )
          markSrc( body, newBody )
          val ret = OperEx( oper, newName, newSet, newBody )
          markSrc( p_ex, ret )
          ret

        /**
          * WARNING: Should not work correctly for unbounded quantifiers, (Jure, 23.7.2018)
          **/
        case OperEx( oper, args@_* ) =>
          val newArgs = args.map( lambda( p_boundVars, p_prefix ) )
          args.zip( newArgs ) foreach { case (oldVal, newVal) => markSrc( oldVal, newVal ) }
          val ret = OperEx( oper, newArgs : _* )
          markSrc( p_ex, ret )
          ret
        case _ => p_ex
      }
    }

    p_decls.map(
      _ match {
        case TlaOperDecl( name, params, body ) =>
          TlaOperDecl( name, params.map( renameParam( name ) ), lambda( params.map( _.name ).toSet, name )( body ) )
        case decl@_ => decl
      }
    )

  }


  /** Stores the operator declared by decl in the BodyDB */
  def extract( p_decls : TlaDecl*) : Unit = p_decls foreach {
    _ match {
      case TlaOperDecl( name, params, body ) if !m_bodyDB.contains( name ) =>
        identify( body )
        m_bodyDB.update( name, (params, body) )
      case _ => ()
    }
  }

  def unfoldOnce:  TlaEx => TlaEx = {
    /**
      * Bug( Jure: 15.1.2018 ): Inlining did not look inside the operator declarations of a LET-IN
      * operator.
      */

    def subAndID( p_operEx : TlaEx ) : TlaEx = {
      def lambda( name : String, args : TlaEx* ) : TlaEx =
        m_bodyDB.get( name ) match {
          case None => p_operEx
          case Some((params, body)) =>
            if ( params.size != args.size )
              throw new IllegalArgumentException(
                "Operator %s with arity %s called with %s argument%s".format( name, params.size, args.size, if ( args.size != 1 ) "s" else "" )
              )
            /** Instantiate all parameters with the corresponding args */
            params.zip(args).foldLeft( body ){
              case (oldBody, (param, arg)) =>
                val mid = replaceAll( oldBody, NameEx(param.name), arg )
                markSrc( oldBody, mid ) /** Should we keep all intermediate TlaEx? */
                mid
            }
//            markSrc( p_operEx, newBody )
        }

      /** On UserOpers or applications, replace, otherwise ignore */
      p_operEx match {
        case OperEx( op : TlaUserOper, args@_* ) =>
          val newEx = lambda( op.name, args : _* )
          markSrc(p_operEx, newEx)
          newEx
        case OperEx( TlaOper.apply, NameEx( name ), args@_* ) =>
          val newEx = lambda( name, args : _* )
          markSrc(p_operEx, newEx)
          newEx
        /**
          * 0-arity operators should never appear as only a NameEx, since recursion looks at children before
          * the parent expression. This would trigger an arity exception since, at the subtree,
          * the arguments are not visible.
          * */
//        case NameEx(name) =>
//          val newEx = lambda( name )
//          markSrc(p_operEx, newEx)
//          newEx
        case _ => p_operEx
      }
    }

    def unification(p_ex: TlaEx,p_children: Traversable[TlaEx]): TlaEx = subAndID(
      p_ex match {
        case OperEx( oper, args@_* ) =>
          if ( args == p_children ) // in case of no-op, do not reconstruct OperEx
            p_ex
          else {
            val ret = OperEx( oper, p_children.toSeq : _* )
            identify(ret)
            ret
          }
        case _ => p_ex
      }
    )

    RecursiveProcessor.computeFromTlaEx(
      RecursiveProcessor.DefaultFunctions.naturalTermination,
      subAndID,
      subAndID,
      unification
    )

//    RecursiveProcessor.transformTlaEx(
//      RecursiveProcessor.DefaultFunctions.naturalTermination,
//      subAndID,
//      subAndID
//    )
//    markSrc( p_ex, ret, p_srcDB )
  }

  def unfoldMax: TlaEx => TlaEx = RecursiveProcessor.computeFixpoint[TlaEx](
    unfoldOnce, RecursiveProcessor.DefaultFunctions.equality[TlaEx]
  )(_).getOrElse(NullEx)

  def replaceAll( p_tlaEx : TlaEx,
                  p_replacedEx : TlaEx,
                  p_newEx : TlaEx
                ) : TlaEx = {
    def swap( arg : TlaEx ) : TlaEx = {
      val ret = p_newEx.deepCopy( identified = false )
      identify( ret )
      markSrc( arg, ret )
      ret
    }

    RecursiveProcessor.transformTlaEx(
      _ == p_replacedEx,
      swap,
      RecursiveProcessor.DefaultFunctions.identity[TlaEx]
    )(p_tlaEx)
  }

  def print( ) : Unit = m_uidDB.print()

}

