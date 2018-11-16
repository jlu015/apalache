package at.forsyte.apalache.tla.bmcmt.types


import at.forsyte.apalache.tla.bmcmt.{InternalCheckerError, InvalidTlaExException}
import at.forsyte.apalache.tla.bmcmt.types.Signatures.{Poly, Signature}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.TlaUserOper
import at.forsyte.apalache.tla.lir.values._
import NamesAndTypedefs._
import StatelessFunctions._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}

import scalaz.State
import scalaz.Scalaz._
import com.microsoft.z3.Context

abstract class SMTInterface {
  def declareConst(constName: String, constType: String) : void

  def assertSMT( expr: SmtExpr ) : void

  def assertSoftSMT( expr: SmtExpr, weight: Int, id: String) : void = ().point[SpecState]

  def isSat : SpecState[Boolean]
}

sealed case class ConcreteInterfaceZ3( default_soft_asserts: Boolean = true ) extends SMTInterface {
  def z3CommandUnsafe(cmd: String, args: String*)(implicit terminator: String = "") : String =
    argsInParens( cmd +: args :_*) + terminator

  def z3LineCommandUnsafe(cmd: String, args: String*) : String =
    z3CommandUnsafe(cmd, args:_*)(terminator = "\n")

  def declareConst(constName: String, constType: String = typeName) : void = modify[SmtInternal] {
    _ + z3LineCommandUnsafe( "declare-const", constName, constType )
  }

  def declareDatatypes() : void = modify[SmtInternal] {
    val types : List[String] = List(
      intTypeName,
      boolTypeName,
      strTypeName,
      z3CommandUnsafe( varTypeName, z3CommandUnsafe( varAccessorName, z3Int ) ),
      z3CommandUnsafe( setTypeName, z3CommandUnsafe( setAccessorName, typeName ) ),
      z3CommandUnsafe( seqTypeName, z3CommandUnsafe( seqAccessorName, typeName ) ),
      z3CommandUnsafe( recTypeName, z3CommandUnsafe( recAccessorName, z3Int) ),
      z3CommandUnsafe( tupTypeName, z3CommandUnsafe( tupAccessorName, z3Int) ),
      z3CommandUnsafe( funTypeName, z3CommandUnsafe( argAccessorName, z3Int), z3CommandUnsafe(resAccessorName, z3Int) )
    )

    _ + z3LineCommandUnsafe(
        "declare-datatypes",
        emptyArg,
        argsInParens(
          z3CommandUnsafe(
            typeName,
            types :_*
          )
        )
      )
  }

  def addFunctions() : void = modify[SmtInternal] {
    _ +
//      z3LineCommandUnsafe( "declare-fun", unknownVarFunName, argsInParens( z3Int ), typeName ) +
//      z3LineCommandUnsafe( "declare-fun", labelTypeFunName, argsInParens( z3Int ), typeName ) +
      z3LineCommandUnsafe( "declare-fun", recFieldFunName, argsInParens( z3Int, z3Str, typeName ), z3Bool ) +
      z3LineCommandUnsafe( "declare-fun", tupIdxFunName, argsInParens( z3Int, z3Int, typeName ), z3Bool ) +
      z3LineCommandUnsafe( "declare-fun", tupSizeFunName, argsInParens( z3Int ), z3Int ) +
      z3LineCommandUnsafe(
        "define-fun",
        isVarFunName,
        argsInParens( z3CommandUnsafe( "x", typeName ) ),
        z3Bool,
        Exists( List( ArgList("i", z3Int) ), Eql( "x", ArgList(varTypeName, "i") ) ).toString
      )
  }

  def addAxioms() : void = {
    val (i, j, s, t1, t2) = ("i", "j", "s", "t1", "t2")
    // name : dom -> ?? is injective
    def injAxiom(name: String, dom: String) =
      Forall(
        List( ArgList(i, dom), ArgList(j, dom) ),
        Impl( Eql( ArgList( name, i ), ArgList( name, j) ), Eql( i, j ) )
      )

    def uniqueField( sType: String, name: String ) =
      Forall(
        List( ArgList(i, z3Int), ArgList(s, sType), ArgList(t1, typeName), ArgList( t2, typeName ) ),
        Impl(
          And( ArgList( name, i, s, t1 ), ArgList( name, i, s, t2 ) ),
          Eql( t1, t2 )
        )
      )

    for {
      _ <- assertSMT( injAxiom( varTypeName, z3Int ) )
      _ <- assertSMT( injAxiom( recTypeName, z3Int ) )
      _ <- assertSMT( injAxiom( tupTypeName, z3Int ) )
      _ <- assertSMT( uniqueField( z3Str, recFieldFunName ) )
      _ <- assertSMT( uniqueField( z3Int, tupIdxFunName) )
      _ <- assertSMT(
        Forall(
          List( ArgList( i, z3Int ), ArgList( j, z3Int ), ArgList( t1, typeName ) ),
          Impl(
            ArgList( tupIdxFunName, i, j, t1 ),
            Geql( ArgList( tupSizeFunName, i ), j )
          )
        )
      )
    } yield ()
  }

  def addTlaVariableConstants( varNames: List[String] ) : void = {
    val modNames = (varNames ++ (varNames map primeVarNameMod) ) map varNameMod
    for {
      _ <- modNames traverseS {
        declareConst( _, typeName )
      }
      _ <- if(default_soft_asserts) modNames traverseS {
        preferVar
      } else List.empty[Unit].point[SpecState]
    } yield ()
  }

  def addFreshVariablePreferences() : void = for {
    vars <- gets[SmtInternal, Int] {
      _.nextVar
    } map {
      Range( 0, _ ).toList map { i =>
        varNameMod( i.toString )
      }
    }
//    _ <- vars traverseS { declareConst(_, typeName) }
    _ <- if(default_soft_asserts) vars traverseS {
      preferVar
    } else List.empty[Unit].point[SpecState]
  } yield ()


  def closing(): void = modify[SmtInternal] {
    _ + z3LineCommandUnsafe("check-sat") + z3LineCommandUnsafe("get-model")
  }

  def assertSMT( expr: SmtExpr ) : void = modify[SmtInternal] {
    _ + z3LineCommandUnsafe( "assert", expr.toString )
  }

  override def assertSoftSMT( expr: SmtExpr, weight: Int = 1, id: String = defaultIdTagName ) : void = modify[SmtInternal] {
    _ + z3LineCommandUnsafe( "assert-soft", expr.toString, idTag, id, weightTag, weight.toString )
  }

  def preferVar( name: String ) : void = assertSoftSMT( ArgList( isVarFunName, name ) )

  def isSat : SpecState[Boolean] = gets[SmtInternal, Boolean] { s =>
    val ctx = new Context()
    val solver = ctx.mkSolver()
    println(s.partialSpec)
    solver.add( ctx.parseSMTLIB2String( s.partialSpec, null, null, null, null ) )
    solver.check.toString == "SATISFIABLE"
  }

  private def freshVar : SpecState[String] = for {
    name <- State[SmtInternal, String] {
      s => (s.inc, varNameMod( s"${s.nextVar}" ))
    }
    _ <- declareConst( name, typeName )
  } yield name

//  def getTemplate( tlaOperDecl: TlaOperDecl  ) : SpecState[templateType] = for {
//    templateOpt <- gets[SmtInternal, Option[templateType]] { _.knownTemplates.get( tlaOperDecl.name ) }
//    template <- templateOpt match {
//      case Some( t ) =>
//        t.point[SpecState]
//      case None =>
//        val newTemplate = computeTemplate(tlaOperDecl)
//        modify[SmtInternal] { s =>
//          s.copy( knownTemplates = s.knownTemplates + ( tlaOperDecl.name -> newTemplate ) )
//        } map { _ => newTemplate}
//    }
//  } yield template

  def dummyTemplate: templateType = (p : String, q : List[String] ) => True.asInstanceOf[SmtExpr].point[SpecState]

  def dummyTemplateCall : SpecState[templateType] = dummyTemplate.point[SpecState]

  def nabla(vname: String, psi: TlaEx, m: NameMap ) : SpecState[SmtExpr] = psi match {
    case ValEx( TlaInt( _ ) ) => Eql( vname, intTypeName ).asInstanceOf[SmtExpr].point[SpecState]
    case ValEx( TlaStr( _ ) ) => Eql( vname, strTypeName ).asInstanceOf[SmtExpr].point[SpecState]
    case ValEx( TlaBool( _ ) ) => Eql( vname, boolTypeName ).asInstanceOf[SmtExpr].point[SpecState]
    case OperEx( TlaActionOper.prime, NameEx( n ) ) => Eql( vname, primeVarNameMod( varNameMod( n ) ) ).asInstanceOf[SmtExpr].point[SpecState]
    case NameEx( n ) => Eql( vname, m(n) ).asInstanceOf[SmtExpr].point[SpecState]
    case ex@OperEx( oper, args@_*) => for {
      mNew <- boundVariableMap( ex ) map {m ++ _}
      frees <- args.toList traverseS { a =>
        freshVar map { (a, _) }
      }
      subNablas <- frees traverseS { case (a,f) =>
        nabla(f, a, mNew)
      }
      operTempl <- oper match {
          // TODO
        case t : TlaUserOper => dummyTemplateCall
        case _ => dummyTemplateCall
      }
      templateCall <- operTempl( vname, frees map { _._2})

    } yield And( templateCall +: subNablas :_* )
    case _ =>
      throw new InternalCheckerError(s"deltaTilde applied to unexpected expression: ${psi}")
  }
  
//  def templateFromSig( operEx: OperEx ) : (String, List[String]) => SpecState[SmtExpr] = { (e,ts) =>
//    val sigs = Signatures get operEx match {
//      case s : Signature => List(s)
//      case Poly( ss ) => ss
//    }
//    sigs traverseS { case Signature( tps, args, res ) =>
//      tps traverseS {
//        tp => freshVar map { tp -> _ }
////
////          for {
////          fresh <- freshVar
////          _ <- declareConst( fresh, typeName )
////        } yield tp -> fresh
//      } map {
//        _.toMap
//      } map { f =>
//        And(delta( e, res, f) +: (ts.zip(args) map { case (ti, xi) => delta(ti, xi, f) }) :_*)
//      }
//    } map { l =>
//      Or( l:_* )
//    }
//  }

//  def constraintFromSig(tlaEx: TlaEx) : void = tlaEx match {
//    // This should never happen, but it's a legal TlaEx
//    case NullEx =>
//      throw new InvalidTlaExException( "NullEx present during type inference step", tlaEx )
//    // For constants, the type is clear.
//    case ValEx( value ) =>
//      val terminalType = value match {
//        case TlaInt( _ ) => intTypeName
//        case TlaBool( _ ) => boolTypeName
//        case TlaStr( _ ) => strTypeName
//        case _ =>
//          throw new InvalidTlaExException( "Tla value type not supported", tlaEx )
//      }
//      assertSMT( Eql(
//        ArgList( unknownVarFunName, tlaEx.ID.id.toString ),
//        terminalType
//      ) )
//
//    /** TODO: Currently does not consider variable locality (eg from a NameEx belonging to a \Exists bound variable */
//    // Standalone NameEx expressions refer to current-state variables. We therefore enforce the uniform typing
//    // of each variable across all of its instances.
//    case NameEx( n ) =>
//      assertSMT( Eql(
//        ArgList( unknownVarFunName, tlaEx.ID.id.toString ),
//        varNameMod( n )
//      ) )
//    // Similar for primed variables
//    case ex@OperEx( TlaActionOper.prime, NameEx( n ) ) =>
//      assertSMT( Eql(
//        ArgList( unknownVarFunName, ex.ID.id.toString ),
//        varNameMod( primeVarNameMod( n ) )
//      ) )
//    // For every other operator the signature tells us how to instantiate isType predicates (see paper)
//    case ex@OperEx( oper, args@_* ) => oper match {
//      case op: TlaUserOper =>
//        for {
//          freshvars <- op.decl.formalParams traverseS { p =>
//            freshVar map { p.name -> _ }
//          } map {_.toMap}
//        } yield ()
//
//      case _ =>
//        val template = templateFromSig( ex )
//        val arity = args.size + 1
//        for {
//          expr <- template( "qq", Range( 0, arity ).toList map { i => s"qq_${i}" } )
//          _ <- assertSMT( expr )
//        } yield ()
//    }
//  }

  def specFramework( variableNames: List[String] )( cmp: void ): SpecState[Boolean] = for {
    _ <- declareDatatypes()
    _ <- addFunctions()
    _ <- addAxioms()
    _ <- addTlaVariableConstants( variableNames )
    _ <- cmp
    _ <- addFreshVariablePreferences()
    //      _ <- closing() // NOTE: z3 implementation doesn't seem to want this in the parsed spec.
    sat <- isSat
  } yield sat

//  def toplevelOperatorSpec( decl: TlaOperDecl ) : void = decl match {
//    case TlaOperDecl( name, params, body ) =>
//      for {
//        _ <- (name +: ( params map {_.name} ) map {s => s"toplevel_$s"}) traverseS {declareConst(_,typeName)}
//        _ <- constraintFromSig( body )
//      } yield ()
//  }



  def boundVariableMap( operEx: OperEx ) : SpecState[NameMap] = operEx match {
    case OperEx( TlaBoolOper.forall | TlaBoolOper.exists | TlaOper.chooseBounded , NameEx( i ), _, _ ) =>
      freshVar map { s => Map(i -> s) }
    case _ => Map.empty[String,String].point[SpecState]
  }

}