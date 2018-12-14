package at.forsyte.apalache.tla.bmcmt.types


import at.forsyte.apalache.tla.bmcmt.{InternalCheckerError, InvalidTlaExException}
import at.forsyte.apalache.tla.bmcmt.types.Signatures.{Poly, Signature}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.TlaUserOper
import at.forsyte.apalache.tla.lir.values._
import NamesAndTypedefs.{SpecState, _}
import StatelessFunctions._
import at.forsyte.apalache.tla.bmcmt.types.CounterStates.{CounterState, CounterType}
import at.forsyte.apalache.tla.lir.control.{LetInOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.oper._

import scalaz.State
import scalaz.Scalaz._
import com.microsoft.z3.Context

import scala.collection.immutable.SortedMap

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
      z3CommandUnsafe( funTypeName, z3CommandUnsafe( argAccessorName, typeName), z3CommandUnsafe(resAccessorName, typeName) ),
      z3CommandUnsafe( operTypeName, z3CommandUnsafe( oargAccessorName, typeName), z3CommandUnsafe(oresAccessorName, typeName) )
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
            Geq( ArgList( tupSizeFunName, i ), j )
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
//    println(s.partialSpec)
    solver.add( ctx.parseSMTLIB2String( s.partialSpec, null, null, null, null ) )
    solver.check.toString == "SATISFIABLE"
//    true
  }

  def runCounterStateVar[T]( cs: CounterState[T] ) : SpecState[T] = State[SmtInternal, T] { s =>
    val (j, ret) = cs.run( s.nextVar )
    (s.copy( nextVar = j ), ret )
  }

  def runCounterStateBound[T]( cs: CounterState[T] ) : SpecState[T] = State[SmtInternal, T] { s =>
    val (j, ret) = cs.run( s.nextBound )
    (s.copy( nextBound = j ), ret )
  }


  def freshVar : SpecState[String] = for {
    name <- State[SmtInternal, String] {
      s => (s.inc, varNameMod( s"${s.nextVar}" ))
    }
    _ <- declareConst( name, typeName )
  } yield name

  def freshBoundVar : SpecState[String] =
    State[SmtInternal, String] {
      s => (s.incB, s"i_${s.nextBound}")
    }

  def linkedFreshVar( uid : UID ) : SpecState[String] = for {
    name <- freshVar
    _ <- modify[SmtInternal] {
      s => s.copy( labelMap = s.labelMap + (name -> uid) )
    }
  } yield name

  protected def nFresh(n: Int) : SpecState[TypeMap] =
    Range(0,n).toList traverseS { i =>
      freshVar map { s => alphaT(i) -> strToSmtConst( s ) }
    } map { _.toMap }

  protected def nLinkedFresh(n: Int, uid: UID) : SpecState[TypeMap] =
    Range(0,n).toList traverseS { i =>
      linkedFreshVar(uid) map { s => alphaT(i) -> strToSmtConst( s ) }
    } map { _.toMap }



  sealed case class PreDelta( m: TypeMap, typeLst: List[SmtType] )

  def templateFromOper( p_ex : OperEx ) : SmtTemplate = {
    val f : templateType =
      ( tBody : String, tsArgs : List[String] ) => {
        val allts = tBody +: tsArgs

        def joinDeltas( pd: PreDelta ) : CounterState[SmtExpr] =
          ( allts zip pd.typeLst ) traverseS { case (x, t) =>
            delta( x, t, pd.m )
          } map {
            And( _ : _* )
          }

        def resolveOverload( pds: List[PreDelta] ) : SpecState[SmtExpr] =
          runCounterStateBound( pds traverseS joinDeltas map {
              case h :: Nil => h
              case lst => Or( lst : _* )
          } )

        implicit def singletonList( e: PreDelta ): List[PreDelta] = List( e )

        val pds : SpecState[List[PreDelta]] = p_ex.oper match {
          // Logic
          case TlaOper.eq | TlaOper.ne =>
            val List( tLhs, tRhs ) = tsArgs
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( boolT, alphaT( 0 ), alphaT( 0 ) )
              )
            }

          case TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.implies | TlaBoolOper.equiv | TlaBoolOper.not =>
            PreDelta(
              m = Map.empty,
              typeLst = allts map { _ => boolT }
            ).point[List].point[SpecState]

          case TlaBoolOper.exists | TlaBoolOper.forall =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( boolT, alphaT( 0 ), setT( alphaT( 0 ) ), boolT )
              )
            }

          case TlaOper.chooseBounded =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( alphaT( 0 ), alphaT( 0 ), setT( alphaT( 0 ) ), boolT )
              )
            }

          case TlaOper.chooseIdiom =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( alphaT( 0 ), setT( alphaT( 0 ) ) )
              )
            }

          // Arithmetic
          case TlaArithOper.plus | TlaArithOper.minus | TlaArithOper.mult | TlaArithOper.div | TlaArithOper.mod =>
            PreDelta(
              m = Map.empty,
              typeLst = allts map { _ => intT }
            ).point[List].point[SpecState]

          case TlaArithOper.dotdot =>
            PreDelta(
              m = Map.empty,
              typeLst = List( setT( intT ), intT, intT )
            ).point[List].point[SpecState]

          case TlaArithOper.lt | TlaArithOper.gt | TlaArithOper.le | TlaArithOper.ge =>
            PreDelta(
              m = Map.empty,
              typeLst = List( boolT, intT, intT )
            ).point[List].point[SpecState]

          // Sets
          case TlaSetOper.in | TlaSetOper.notin =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( boolT, alphaT( 0 ), setT( alphaT( 0 ) ) )
              )
            }

          case TlaSetOper.subseteq | TlaSetOper.subsetProper | TlaSetOper.supseteq | TlaSetOper.supsetProper =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( boolT, setT( alphaT( 0 ) ), setT( alphaT( 0 ) ) )
              )
            }

          case TlaSetOper.cap | TlaSetOper.cup | TlaSetOper.setminus =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( setT( alphaT( 0 ) ), setT( alphaT( 0 ) ), setT( alphaT( 0 ) ) )
              )
            }

          case TlaSetOper.enumSet =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = setT( alphaT( 0 ) ) +: ( tsArgs map { _ => alphaT( 0 ) } )
              )
            }

          case TlaSetOper.filter =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( setT( alphaT( 0 ) ), alphaT( 0 ), setT( alphaT( 0 ) ), boolT )
              )
            }

          // Arg order: e, (x, S)+
          case TlaSetOper.map =>
            // map takes 2n + 1 args, the 1st is the expression, followed by n element-set pairs
            // We need n+1 type parameters
            val n = ( p_ex.args.size - 1 ) / 2
            nFresh( n + 1 ) map { m =>
              PreDelta(
                m = m,
                typeLst = List( setT( alphaT( n ) ), alphaT( n ) ) ++:
                  ( Range( 0, n ).toList flatMap { i =>
                    List( alphaT( i ), setT( alphaT( i ) ) )
                  } )
              )
            }

          case TlaSetOper.powerset =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( setT( setT( alphaT( 0 ) ) ), setT( alphaT( 0 ) ) )
              )
            }

          case TlaSetOper.union =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( setT( alphaT( 0 ) ), setT( setT( alphaT( 0 ) ) ) )
              )
            }

          case TlaFiniteSetOper.cardinality =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( intT, setT( alphaT( 0 ) ) )
              )
            }
          // Functions
          case TlaFunOper.domain =>
            nFresh( 2 ) map { m =>
              PreDelta(
                m = m,
                typeLst = List( setT( alphaT( 0 ) ), funT( alphaT( 0 ), alphaT( 1 ) ) )
              )
            }

          // Arg order: e, (x,S)+
          case TlaFunOper.funDef =>
            // funDef takes 2n + 1 args, the 1st is the expression, followed by n element-set pairs
            // We need n+1 type parameters
            val n = ( p_ex.args.size - 1 ) / 2
            nFresh( n + 1 ) map { m =>
              // The domain is a tuple <=> n + 1 > 2 <=> n > 1

              val domain =
                if(n > 1)
                  tupT( Range( 0, n ).toList map alphaT )
                else
                  alphaT(0)

              PreDelta(
                m = m,
                typeLst = List( funT( domain, alphaT( n ) ), alphaT( n ) ) ++:
                  ( Range( 0, n ).toList flatMap { i =>
                    List( alphaT( i ), setT( alphaT( i ) ) )
                  } )
              )
            }

          case TlaSetOper.funSet =>
            nFresh( 2 ) map { m =>
              PreDelta(
                m = m,
                typeLst = List( setT( funT( alphaT( 0 ), alphaT( 1 ) ) ), setT( alphaT( 0 ) ), setT( alphaT( 1 ) ) )
              )
            }

          // Overloaded

          case TlaFunOper.except =>
            // except takes 2n + 1 args, the 1st is the function, followed by n key-value pairs
            // each key is a m-size tuple
            // We need m + 1 type parameters
            val n = ( p_ex.args.size - 1 ) / 2

            val keys = p_ex.args.toList.tail.zipWithIndex filter {
              case (_, j) => j % 2 == 0
            }

            val mOpt = (keys map {
              case (OperEx( TlaFunOper.tuple, args@_* ), _) => args.size
              case _ => -1
            }).distinct match {
              case emm :: Nil if emm > 0 => Some(emm)
              case _ => None
            }

            if ( mOpt.empty ) throw new InternalCheckerError(s"EXCEPT arguments in ${p_ex} are not tuples")

            val emm = mOpt.get

            val recOpt = (keys map {
              /** Records CANNOT use currying */
              case ( OperEx( TlaFunOper.tuple, ValEx( TlaStr( s ) ) ), _) => if( emm == 1) Some(s) else None
              case _ => None
            } ).sequence

            nFresh( (emm + 1) + n ) map { m =>
              val recpd = recOpt map { ks =>
                val recMap = SortedMap(ks zip Range(emm + 1, emm + n + 1) map { case (k,j) =>
                  k -> alphaT( j )
                } :_*)
                List(
                  PreDelta(
                    m = m,
                    typeLst = List.fill( 2 )( recT( recMap ) ) ++:
                      ( Range( emm + 1, emm + n + 1 ).toList flatMap { j => List( tupT( List( strT ) ), alphaT( j ) ) })
                  )
                )
              }
              val mFold = Range(0,emm).reverse.foldLeft[SmtType]( alphaT( emm ) ){ case (a, j) => funT( alphaT(j), a ) }
              recpd.getOrElse( List.empty[PreDelta] ) ++: List(
                // Fun
                PreDelta(
                  m = m,
                  typeLst = List.fill( 2 )( mFold ) ++:
                    List.fill( n )( List( tupT( Range( 0, emm ).toList map alphaT ), alphaT( emm ) ) ).flatten
                )
              )
            }
          case TlaFunOper.app =>
            nFresh( 2 + 1 + 1 ) map { m =>
              val basicList = List(
                // Fun
                PreDelta(
                  m = m,
                  typeLst = List( alphaT( 1 ), funT( alphaT( 0 ), alphaT( 1 ) ), alphaT( 0 ) )
                ),
                // Seq
                PreDelta(
                  m = m,
                  typeLst = List( alphaT( 2 ), seqT( alphaT( 2 ) ), intT )
                )
              )
              // for records and tuples we need the actual value of the arg
              val Seq(_, exactArg) = p_ex.args

              val other = exactArg match {
                case ValEx( TlaStr( s ) ) => List(
                  PreDelta(
                    m = m,
                    typeLst = List( alphaT( 3 ), recT( SortedMap( s -> alphaT( 3 ) ) ) , strT )
                  )
                )
                case ValEx( TlaInt( i ) ) => List(
                  PreDelta(
                    m = m,
                    typeLst = List( alphaT( 3 ), sparseTupT( SortedMap( i.toInt -> alphaT( 3 ) ) ), intT )
                  )
                )
                case _ => List.empty[PreDelta]
              }

              other ++: basicList
            }

          case TlaFunOper.tuple =>
            // n = size of tuple
            val n = p_ex.args.size
            nFresh( n + 1 ) map { m =>
              val alphas = Range( 0, n ).toList map alphaT
              List(
                PreDelta(
                  m = m,
                  typeLst = tupT( alphas ) +: alphas
                ),
                PreDelta(
                  m = m,
                  typeLst = seqT( alphaT( n ) ) +: List.fill( n )( alphaT( n ) )
                )
              )
            }

          // Records
          case TlaFunOper.enum =>
            // Enum takes 2n arguments
            // we need n fresh vars
            val n = p_ex.args.size / 2
            val keys = p_ex.args.toList.zipWithIndex filter {
              case (_, j) => j % 2 == 0
            } map {
              case (ValEx( TlaStr( s ) ), _) => s
              case _ => throw new InvalidTlaExException(s"Cannot construct record from ${p_ex}", p_ex )
            }
            nFresh( n ) map { m =>
              val recMap = SortedMap(keys zip m map { case (k,(a,_)) =>
                k -> a
              } :_*)
              PreDelta(
                m = m,
                typeLst = recT( recMap ) +:
                  ( Range( 0, n ).toList flatMap { i => List( strT, alphaT( i ) ) } )
              )
            }

          case TlaSetOper.recSet =>
            // recSet takes 2n args, n key-value pairs
            // We need n type parameters
            val n = p_ex.args.size / 2
            val keys = p_ex.args.toList.zipWithIndex filter {
              case (_, j) => j % 2 == 0
            } map {
              case (ValEx( TlaStr( s ) ), _) => s
              case _ => throw new InvalidTlaExException("Cannot construct record from ", p_ex)
            }
            nFresh( n ) map { m =>
              val recMap = SortedMap(keys zip m map { case (k,(a,_)) =>
                k -> a
              } :_*)
              PreDelta(
                m = m,
                typeLst = setT( recT( recMap ) ) +:
                  ( Range( 0, n ).toList flatMap { i => List( strT, setT( alphaT( i ) ) ) } )
              )
            }

          // Tuples
          case TlaSetOper.times =>
            // n = size of product
            val n = p_ex.args.size
            nFresh( n ) map { m =>
              val alphas = Range( 0, n ).toList map alphaT
              PreDelta(
                m = m,
                typeLst = tupT( alphas ) +: alphas map setT
              )
            }

          // Sequences
          case TlaSeqOper.concat =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List.fill( 3 )( seqT( alphaT( 0 ) ) )
              )
            }
          case TlaSeqOper.head =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( alphaT( 0 ), seqT( alphaT( 0 ) ) )
              )
            }

          case TlaSeqOper.tail =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( seqT( alphaT( 0 ) ), seqT( alphaT( 0 ) ) )
              )
            }

          case TlaSeqOper.len =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( intT, seqT( alphaT( 0 ) ) )
              )
            }

          case TlaSetOper.seqSet =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( setT( seqT( alphaT( 0 ) ) ), setT( alphaT( 0 ) ) )
              )
            }

          case TlaSeqOper.append =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( seqT( alphaT( 0 ) ), seqT( alphaT( 0 ) ), alphaT( 0 ) )
              )
            }

          case TlaSeqOper.subseq =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( seqT( alphaT( 0 ) ), intT, intT, seqT( alphaT( 0 ) ) )
              )
            }


          // Control
          case TlaControlOper.ifThenElse =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( alphaT( 0 ), boolT, alphaT( 0 ), alphaT( 0 ) )
              )
            }
          case TlaControlOper.caseNoOther =>
            // CNO takes 2n arguments
            val n = p_ex.args.size / 2
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = alphaT( 0 ) +: List.fill( n )( List( boolT, alphaT( 0 ) ) ).flatten
              )
            }

          case TlaControlOper.caseWithOther =>
            // CWO takes 2n + 1 args, the 1st is the OTHER, followed by n predicate-branchVal pairs
            val n = (p_ex.args.size - 1) / 2
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List.fill( 2 )( alphaT( 0 ) ) ++: List.fill( n )( List( boolT, alphaT( 0 ) ) ).flatten
              )
            }

          // Operator application
          case TlaOper.apply =>
            p_ex.args.size - 1 match {
              case 0 => freshVar map { f =>
                PreDelta(
                  m = Map( alphaT( 0 ) -> f ),
                  typeLst = List( alphaT( 0 ), alphaT( 0 ) )
                )
              }
              case 1 => nFresh( 2 ) map { m =>
                PreDelta(
                  m = m,
                  typeLst = List( alphaT( 1 ), operT( alphaT( 0 ), alphaT( 1 ) ), alphaT( 0 ) )
                )
              }
              case n => nFresh( n + 1 ) map { m =>
                PreDelta(
                  m = m,
                  typeLst = List( alphaT( n ), operT( tupT( Range( 0, n ).toList map alphaT ), alphaT( n ) ) ) ++:
                    ( Range( 0, n ).toList map alphaT )
                )
              }
            }

            // TLC operators
          case TlcOper.print =>
            freshVar map { f =>
              PreDelta(
                m = Map( alphaT( 0 ) -> f ),
                typeLst = List( alphaT( 0 ), strT, alphaT( 0 ) )
              )
            }

          case TlcOper.colonGreater =>
            nFresh( 2 ) map { m =>
              PreDelta(
                m = m,
                typeLst = List( funT( alphaT( 0 ), alphaT( 1 ) ), alphaT( 0 ), alphaT( 1 ) )
              )
            }

          case TlcOper.atat =>
            nFresh( 2 ) map { m =>
              PreDelta(
                m = m,
                typeLst = List.fill(3)( funT( alphaT( 0 ), alphaT( 1 ) ) )
              )
            }

          case _ =>
            throw new InternalCheckerError( s"Signature for operator [${p_ex.oper.name}] is not implemented" )
        }
//        pds flatMap { p => runCounterStateBound( joinDeltas ( p ) ) }
        pds flatMap resolveOverload
      } : SpecState[SmtExpr]
    SmtTemplate( p_ex.oper.arity, f )
  }

  def dummyTemplate: SmtTemplate = SmtTemplate( AnyArity(),  (p : String, q : List[String] ) => True.asInstanceOf[SmtExpr].point[SpecState] )

  def dummyTemplateCall : SpecState[SmtTemplate] = dummyTemplate.point[SpecState]

  def templateFromDecl( decl: TlaOperDecl, m : NameMap, dm: DeclMap  ) : SmtTemplate = decl match {
    case TlaOperDecl( name, params, body ) =>
      val f : templateType =
        ( tBody : String, tsArgs : List[String] ) => {
          val m_x = (params map { _.name} zip tsArgs).toMap
//          println( s"phi: ${body}" )
          nabla( tBody, body, m ++ m_x, dm )
        } : SpecState[SmtExpr]
      SmtTemplate( decl.operator.arity, f )
  }

  def memoGetTemplate( t: TlaUserOper, m: NameMap, dm: DeclMap )( implicit rememberTemplate : Boolean = true ) : SpecState[SmtTemplate] =
    for {
      templOpt <- gets[SmtInternal, Option[SmtTemplate]] { s =>
        s.knownTemplates.get( t.name )
      }
      ret <- templOpt match {
        case Some( template ) => template.point[SpecState]
        case _ =>
          val templ = templateFromDecl( t.decl, m, dm )
          State[SmtInternal, SmtTemplate] {
            s =>
              if (rememberTemplate)
                (s.copy( knownTemplates = s.knownTemplates + ( t.name -> templ ) ), templ)
              else (s, templ)
          }
      }
    } yield ret

  def instanceOf( vname: String, decl: TlaOperDecl, m: NameMap, dm: DeclMap ) : SpecState[SmtExpr] = {
    val templateS = memoGetTemplate( decl.operator, m, dm )
    decl.formalParams.size match {
      case 0 => templateS flatMap {
        t => t( vname, List.empty )
      }
      case 1 => for {
        g1 <- freshVar
        g2 <- freshVar
        templ <- templateS
        tExpr <- templ( g2, List( g1 ) )
      } yield And( Eql( vname, ArgList( operTypeName, g1, g2 ) ), tExpr )

      case k => for {
        bound <-freshBoundVar
        gs <- Range(0,k+1).toList traverseS { _ => freshVar }
        templ <- templateS
        templEx <- templ( gs.head, gs.tail )
      } yield
        Exists(
          List( ArgList( bound, z3Int ) ),
          And(
            Eql( vname, ArgList( operTypeName, ArgList( tupTypeName, bound ), gs.head ) ),
            Eql( ArgList( tupSizeFunName, bound ), k.toString ),
            templEx,
            And( Range(1, k + 1) zip gs.tail map { case (j, gj) => ArgList( tupIdxFunName, bound, j.toString, gj ) } : _* )
          )
        )
    }
  }



  def nabla(vname: String, psi: TlaEx, m: NameMap, dm : DeclMap )( implicit rememberTemplates : Boolean = true ) : SpecState[SmtExpr] = psi match {
    case ValEx( TlaInt( _ ) ) => Eql( vname, intTypeName ).asInstanceOf[SmtExpr].point[SpecState]
    case ValEx( TlaStr( _ ) ) => Eql( vname, strTypeName ).asInstanceOf[SmtExpr].point[SpecState]
    case ValEx( TlaBool( _ ) ) => Eql( vname, boolTypeName ).asInstanceOf[SmtExpr].point[SpecState]
    case OperEx( TlaActionOper.prime, NameEx( n ) ) => Eql( vname, primeVarNameMod( varNameMod( n ) ) ).asInstanceOf[SmtExpr].point[SpecState]
    case NameEx( n ) =>
      // Case split, n might be an operator name passed to a higher-order operator as an argument
      dm.get( n ) match {
        case Some( decl ) =>
          instanceOf( vname, decl, m, dm)

        case None => m.get( n ) match {
          case Some( smtVar ) => Eql( vname, m( n ) ).asInstanceOf[SmtExpr].point[SpecState]
          case None => throw new InternalCheckerError(s"Free variable $n is neither a TLA+ variable nor an operator name.")
        }
      }
    case OperEx( TlaActionOper.unchanged, arg ) =>
      val primedArg = RecursiveProcessor.transformTlaEx(
        _.isInstanceOf[NameEx],
        {
          case NameEx( n ) => OperEx( TlaActionOper.prime, NameEx( n ) )
          case x => x
        },
        RecursiveProcessor.DefaultFunctions.identity
      )( arg )
      nabla( vname, Builder.eql( primedArg , arg ), m, dm )

    case OperEx( letIn : LetInOper, body ) =>
      val newDm = dm ++ (letIn.defs map { opDef => opDef.name -> opDef } ).toMap
      val newNames = letIn.defs map { _.name }
      for {
        post <- nabla( vname, body, m, newDm )
        _ <- modify[SmtInternal] { s =>
          s.copy( knownTemplates = s.knownTemplates -- newNames )
        }
      } yield post

    case ex@OperEx( oper, args@_*) => for {
      mNew <- boundVariableMap( ex ) map {m ++ _}
      frees <- args.toList traverseS { a =>
        freshVar map { (a, _) }
      }
      operTempl <- oper match {
        case t : TlaUserOper => memoGetTemplate( t, m, dm )( rememberTemplates )

        case _ => templateFromOper( ex ).point[SpecState]
      }
      templateCall <- operTempl( vname, frees map { _._2})
      subNablas <- frees traverseS { case (a,f) =>
        nabla(f, a, mNew, dm)
      }
    } yield And( templateCall +: subNablas :_* )
    case _ =>
      throw new InternalCheckerError(s"deltaTilde applied to unexpected expression: ${psi}")
  }



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

  def boundVariableMap( operEx: OperEx ) : SpecState[NameMap] = operEx match {
    case OperEx( TlaBoolOper.forall | TlaBoolOper.exists | TlaOper.chooseBounded | TlaSetOper.filter , NameEx( i ), _, _ ) =>
      freshVar map { s => Map(i -> s) }
    case OperEx( TlaSetOper.map | TlaFunOper.funDef, _, args@_* ) =>
      val names = args.toList.zipWithIndex filter { case (_,i) => i % 2 == 0  } map { _._1 }
      names traverseS { case NameEx( i ) =>
        freshVar map { i -> _ }
      case e =>
        throw new InternalCheckerError( s"Expected a bound variable name in ${e}" )
      } map { _.toMap }
    case _ => Map.empty[String,String].point[SpecState]
  }

}