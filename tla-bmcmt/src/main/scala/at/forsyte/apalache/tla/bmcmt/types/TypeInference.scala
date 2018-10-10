package at.forsyte.apalache.tla.bmcmt.types

import java.math.RoundingMode

import at.forsyte.apalache.tla.bmcmt.{InternalCheckerError, InvalidTlaExException, TypeException}
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import com.google.common.math.IntMath
import box.setlike.DisjointSets

import scala.collection.immutable.SortedMap
import scala.util.matching.Regex
import scalaz.State
import scalaz.State._
import scalaz.syntax.traverse.ToTraverseOps
import scalaz.std.list.listInstance
import scalaz.std.option._
import scalaz.std.set.setInstance
//import scalaz.Scalaz._
import scalaz.Scalaz.ApplicativeIdV

/**
  * State wrapper around an integer counter, used for guaranteeing unique value generation
  */
object CounterStates {
  type CounterType = Int
  type CounterState[T] = State[CounterType, T]

  def inc( ) : CounterState[CounterType] = State[CounterType, CounterType] {
    s => (s + 1, s)
  }
}

/**
  * Generates Signature instances, describing the various operators of TLAP in terms of their input and output types
  */
object Signatures {

  import CounterStates._

  sealed abstract class Sig

  /**
    * Describres the signature of a TLAP operator.
    *
    * @param typeParams In the case of polymorphic operators, `typeParams` lists the type parameters. Empty if not polymorphic
    * @param args       The sequence of argument types accepted by the operator
    * @param res        The type held by the result of the operator application
    */
  sealed case class Signature( typeParams : List[TypeParam], args : List[MinimalCellT], res : MinimalCellT ) extends Sig{
    override def toString : String = {
      val ts = typeParams map {
        _.signature
      } mkString ", "
      val as = args map {
        _.signature
      } mkString s" ${UTFPrinter.m_times} "
      val prefix = if ( typeParams.isEmpty ) "" else s"${UTFPrinter.m_forall} ${ts} . "
      s"${prefix}${as} ${UTFPrinter.m_rarrow} ${res.signature}"
    }
  }

  sealed case class Poly( sig1: Signature, sig2: Signature, id: CounterType ) extends Sig

  sealed abstract class PolySigBlock {
    import PolySigBlock._
    def &&( other: PolySigBlock ) : PolySigBlock = (this, other) match {
      case (NoBlock, _) => other
      case (_, NoBlock) => this
      case (FullBlock, _) => this
      case (_, FullBlock) => other
      case (LeftBlock, RightBlock) => FullBlock
      case (RightBlock, LeftBlock) => FullBlock
      case _ => this
    }
  }

  object PolySigBlock {

    object NoBlock extends PolySigBlock

    object LeftBlock extends PolySigBlock

    object RightBlock extends PolySigBlock

    object FullBlock extends PolySigBlock

  }

  sealed case class PolyDecisionInfo( c: CounterType  )

  type SigBlockMap = Map[CounterType, List[Int]]


  private def typeParam( exId : UID, id : Int ) : TypeParam = TypeParam( s"${exId.id}_${id}" )

  /**
    * Yields the Signature associated with the given operator.
    *
    * Type parameter names for polymorphic operators are ony unique within the scope of the Signature.
    */
  def get( op : OperEx ) : Sig = getFresh( op ).run( 0 )._2

  /**
    * Yields the Signature associated with the given operator as a State computation.
    *
    * Type parameter names for polymorphic operators unique within the scope of the entire computation.
    */
  def getFresh( op : OperEx ) : CounterState[Sig] = inc() map { i =>
    val exId = op.ID
    /** TODO: Might cause naming clashes with variables named that way !!! */
    val T = TypeParam( s".c_${i}" )

    def ts( n : Int ) : List[TypeParam] = List.range( 1, n + 1 ) map { j =>
      TypeParam( s".c_${i}_${j}" )
    }

    val ts2 = ts( 2 )

    val List( t1, t2 ) = ts2

    val ret = op.oper match {
      // Logic
      case TlaOper.eq | TlaOper.ne =>
        Signature( List( T ), List( T, T ), BoolT() )
      case TlaBoolOper.and | TlaBoolOper.or =>
        Signature( List.empty, List.fill( op.args.size )( BoolT() ), BoolT() )
      case TlaBoolOper.implies | TlaBoolOper.equiv =>
        Signature( List.empty, List.fill( 2 )( BoolT() ), BoolT() )
      case TlaBoolOper.not =>
        Signature( List.empty, List( BoolT() ), BoolT() )
      case TlaBoolOper.exists | TlaBoolOper.forall =>
        Signature( List( T ), List( T, FinSetT( T ), BoolT() ), BoolT() )
      case TlaOper.chooseBounded =>
        Signature( List( T ), List( T, FinSetT( T ), BoolT() ), OptT( T ) )
      case TlaOper.chooseIdiom =>
        Signature( List( T ), List( FinSetT( T ) ), OptT( T ) )

      // Arithmetic
      case TlaArithOper.plus | TlaArithOper.minus | TlaArithOper.mult | TlaArithOper.div | TlaArithOper.mod =>
        Signature( List.empty, List( IntT(), IntT() ), IntT() )
      case TlaArithOper.dotdot =>
        Signature( List.empty, List( IntT(), IntT() ), FinSetT( IntT() ) )
      case TlaArithOper.lt | TlaArithOper.gt | TlaArithOper.le | TlaArithOper.ge =>
        Signature( List.empty, List( IntT(), IntT() ), BoolT() )

      // Sets
      case TlaSetOper.in | TlaSetOper.notin =>
        Signature( List( T ), List( T, FinSetT( T ) ), BoolT() )
      case TlaSetOper.subseteq | TlaSetOper.subsetProper | TlaSetOper.supseteq | TlaSetOper.supsetProper =>
        Signature( List( T ), List.fill( 2 )( FinSetT( T ) ), BoolT() )
      case TlaSetOper.cap | TlaSetOper.cup | TlaSetOper.setminus =>
        Signature( List( T ), List.fill( 2 )( FinSetT( T ) ), FinSetT( T ) )
      case TlaSetOper.enumSet =>
        Signature( List( T ), List.fill( op.args.size )( T ), FinSetT( T ) )
      case TlaSetOper.filter =>
        Signature( List( T ), List( T, FinSetT( T ), BoolT() ), FinSetT( T ) )
      case TlaSetOper.map =>
        Signature( ts2, List( t1, t2, FinSetT( t2 ) ), FinSetT( t1 ) )
      case TlaSetOper.powerset =>
        //        Signature( List( T ), List( FinSetT( T ) ), PowSetT( FinSetT( T ) ) )
        Signature( List( T ), List( FinSetT( T ) ), FinSetT( FinSetT( T ) ) )
      case TlaSetOper.union =>
        Signature( List( T ), List( FinSetT( FinSetT( T ) ) ), FinSetT( T ) )

      // Functions
      case TlaFunOper.app =>
        Signature( ts2, List( FunT( FinSetT( t1 ), t2 ), t1 ), t2 )
      case TlaFunOper.domain =>
        Signature( ts2, List( FunT( t1, t2 ) ), t1 )
      case TlaFunOper.funDef =>
        val n = IntMath.divide( op.args.size, 2, RoundingMode.CEILING ) // ceil( n/2 ) type params
      val nTs = ts( n )
        Signature( nTs, nTs.head :: ( nTs.tail flatMap { t => List( t, FinSetT( t ) ) } ), FunT( CrossProdT( nTs.tail map FinSetT ), nTs.head ) )
      case TlaSetOper.funSet =>
        //        Signature( ts2, ts2 map FinSetT, FinFunSetT( FinSetT( t1 ), FinSetT( t2 ) ) )
        Signature( ts2, ts2 map FinSetT, FinSetT( FunT( FinSetT( t1 ), t2 ) ) )
      case TlaFunOper.except =>
        // except takes 2n + 1 args, the 1st is the function, followed by n element-set pairs
        val n = ( op.args.size - 1 ) / 2
        Signature( ts2, FunT( FinSetT( t1 ), t2 ) +: List.fill( n )( ts2 ).flatten, FunT( FinSetT( t1 ), t2 ) )

      // Records
      case TlaFunOper.enum =>
        val n = op.args.size
        /**  this  can potentially be a record, if all keys are strings */
        val keys = op.args.zipWithIndex filter {
          case (_, j) => j % 2 == 0
        } map {
          case (ValEx( TlaStr( s ) ), _ ) => Some(s)
          case _ => None
        }
        if (keys.forall( _.nonEmpty )) {
          // Poly result
          val nTs = ts( n / 2 + 1 )
          val funT = nTs.head
          val recTs = nTs.tail
          val mp = keys.flatten zip recTs
          val recEnumSig = Signature( recTs, recTs flatMap { t => List( ConstT(), t ) }, RecordT( SortedMap( mp : _* ) ) )
          val funEnumSig = Signature( List( funT ), List.fill( n / 2 )( List(ConstT(), funT) ).flatten, FunT( FinSetT( ConstT() ), funT) )
          Poly( funEnumSig, recEnumSig, i )
        }
        else {
          // Must be a function
          Signature( ts2, List.fill( n / 2 )( ts2 ).flatten, FunT( FinSetT( t1 ), t2 ) )
        }

      // Control
      case TlaControlOper.ifThenElse =>
        Signature( List( T ), List( BoolT(), T, T ), T )
      case TlaControlOper.caseNoOther =>
        Signature( List( T ), List.fill( op.args.size / 2 )( List( BoolT(), T ) ).flatten, OptT( T ) )
      case TlaControlOper.caseWithOther =>
        // CWO takes 2n + 1 args, the 1st is the OTHER, followed by n predicate-branchVal pairs
        val n = ( op.args.size - 1 ) / 2
        Signature( List( T ), T +: List.fill( n )( List( BoolT(), T ) ).flatten, T )

      // Actions
      case TlaActionOper.prime => // The generic prime accepts any input type and can yield any output type
        Signature( ts2, List( t1 ), t2 )

      case _ =>
        throw new InternalCheckerError( s"Signature for operator [${op.oper.name}] is not implemented" )
      //        Signature( List.empty, List.empty, UnknownT() )
    }
    // Sanity check
    ret match {
      case Signature( _, args, _ ) =>
        assert( op.oper.isCorrectArity( args.size ) )
      case Poly( sig1, sig2, _ ) =>
        List(sig1, sig2) foreach { el =>
          assert( op.oper.isCorrectArity( el.args.size ) )
        }
    }

    ret
  }

}

/**
  * Offers methods for type inference.
  */
object TypeInference {

  import CounterStates._
  import Signatures.{Signature, Poly, PolySigBlock, SigBlockMap}

  private object Internals {

    /**
      * An isType predicate establishes a type equivalence between `v1` and `v2`
      */
    sealed case class isType( v1 : MinimalCellT, v2 : MinimalCellT )

    /** TODO: Might cause naming clashes with variables named that way !!! */
    def newVar( id : UID ) : TypeParam = TypeParam( s".b_${id.id}" )

    def newVar( ex : TlaEx ) : TypeParam = newVar( ex.ID )

    /**
      * Internal computation for the theta function from the paper.
      */
    def thetaS( tlaEx : TlaEx ) : CounterState[List[isType]] = tlaEx match {
      // This should never happen, but it's a legal TlaEx
      case NullEx =>
        throw new InvalidTlaExException( "NullEx present during type inference step", tlaEx )
      // For constants, the type is clear.
      case ValEx( value ) =>
        val terminalType = value match {
          case TlaInt( _ ) => IntT()
          case TlaBool( _ ) => BoolT()
          case TlaStr( _ ) => ConstT()
          case _ =>
            throw new InvalidTlaExException( "Tla value type not supported", tlaEx )
        }
        List( isType( newVar( tlaEx ), terminalType ) ).point[CounterState]


      /** TODO: Currently does not consider variable locality (eg from a NameEx belonging to a \Exists bound variable */
      // Standalone NameEx expressions refer to current-state variables. We therefore enforce the uniform typing
      // of each variable across all of its instances.
      case NameEx( n ) =>
        List( isType( newVar( tlaEx ), TypeParam( s"${n}" ) ) ).point[CounterState]
      // Similar for primed variables
      case ex@OperEx( TlaActionOper.prime, NameEx( n ) ) =>
        List( isType( newVar( ex ), TypeParam( s"${n}'" ) ) ).point[CounterState]
      // For every other operator the signature tells us how to instantiate isType predicates (see paper)
      case ex : OperEx => for {
        sig <- Signatures getFresh ex
        bl = newVar( ex )
        bls = ex.args map newVar
        lst = sig match {
          case Signature( _, args, res ) =>
            isType( bl, res ) +: ( bls.zip( args ) map { case (a, b) => isType( a, b ) } )
          case Poly( sig1, sig2, i ) =>
            val List(th1, th2) = List(sig1, sig2) map { case Signature( _, args, res ) =>
              isType( bl, res ) +: ( bls.zip( args ) map { case (a, b) => isType( a, b ) } )
            }
            th1.zip( th2 ).map { case (isType( x, a ), isType( _, b )) => // the 1st component is identical by construction
              isType( x, XOR( a, b ) )
            }
        }
        subThetas <- ex.args.toList.traverseS( thetaS ).map {
          _.flatten
        }
      } yield lst ++: subThetas
    }

    // The theta call merely runs the computation from the counter value 0
    def theta( tlaEx : TlaEx ) : List[isType] = thetaS( tlaEx ).run( 0 )._2


    type M = Map[TypeParam, MinimalCellT]
    type D = DisjointSets[TypeParam]
    type X = Map[TypeParam, List[TypeParam]]

    sealed case class internal( m : M, d : D, c : CounterType, x: X )

    type MDCX = internal
    type internalState[T] = State[MDCX, T]

    def xorSymm( t1 : MinimalCellT, t2 : MinimalCellT, other : MinimalCellT ) : Option[MinimalCellT] =
      List( (t1, other), (t2, other) ) map {
        case (x, y) => unify( x, y )
      } filter {
        _.nonEmpty
      } match {
        case List( el ) => // unifies with exactly one
          el
        case List( el1, el2 ) => // unifies with both
          if (el1 == el2) el1
          else Some( XOR( el1.get, el2.get ) )
        case _ => None
      }


    def unify( a : MinimalCellT, b : MinimalCellT ) : Option[MinimalCellT] = (a, b) match {
      // \forall x . u(x,x) = x
      case _ if a == b =>
        Some( a )

      // TypeParameters can be unified with everything
      case (TypeParam( _ ), _) =>
        Some( b )
      case (_, TypeParam( _ )) =>
        Some( a )

      // Sets unify recursively
      case (FinSetT( l : MinimalCellT ), FinSetT( r : MinimalCellT )) =>
        unify( l, r ) map FinSetT

      // Functions unify recursively
      case (FunT( lDom : MinimalCellT, lCoDom : MinimalCellT ), FunT( rDom : MinimalCellT, rCoDom : MinimalCellT )) =>
        for {
          dom <- unify( lDom, rDom )
          coDom <- unify( lCoDom, rCoDom )
        } yield FunT( dom, coDom )

      // Tuples unify recursively, if their lengths are the same.
      // If any component doesn't unify, the tuple doesn't unify
      case (TupleT( lArgs : Seq[MinimalCellT] ), TupleT( rArgs : Seq[MinimalCellT] )) =>
        // in contrast to sequences, tuples of different lengths cannot be unified
        if ( lArgs.lengthCompare( rArgs.length ) == 0 )
        // the .sequence method turns List[Option[X]] into an Option[List[X]], where the value is None
        // iff any element of the list is None
          ( lArgs.zip( rArgs ) map { case (x, y) => unify( x, y ) } ).toList.sequence map TupleT
        else
          None

      case (RecordT( lMap : Map[String, MinimalCellT] ), RecordT( rMap : Map[String, MinimalCellT] )) =>
        // We unify only on the keys in both maps
        ( lMap.keySet.intersect( rMap.keySet ) map { k =>
          unify( lMap( k ).asInstanceOf[MinimalCellT], rMap( k ).asInstanceOf[MinimalCellT] ) map { m =>
            k -> m
          }
          // A List[Options[(String,MinimalCellT)]] becomes Option[List[(String, MinimalCellT)]]
        } ).toList.sequence.map {
          _.toMap
        } map { m =>
          // We keep all other key/value pairs and overwrite the unified ones
          ( lMap ++ rMap ) ++ m // ++ order guarantees keys from m (the rhs) dominate
        } map RecordT

      case (XOR( t1, t2 ), other) =>
        xorSymm( t1, t2, other )
      case (other, XOR( t1, t2 )) =>
        xorSymm( t1, t2, other )

      case _ =>
        None
    }

    def follow(el: TypeParam, map: M): MinimalCellT =
      map.getOrElse( el, el ) match {
        case t: TypeParam => if (t == el) t else follow(t, map)
        case t => t
      }

    sealed case class cleanupState( d: D, deadBranch: Boolean )

    def internalFindCleanup( el : TypeParam ) : State[cleanupState, TypeParam] = State[cleanupState, TypeParam] {
      st =>
        val (newD, e) = st.d.find( el )
        (st.copy( d = newD ), e)
    }

    def setDeadBranch(v: Boolean): State[cleanupState, Unit] = modify[cleanupState] {
      s => s.copy( deadBranch = v )
    }

    type CS[T] = State[cleanupState, T]

    /**
      * Cleanup step, in the the final map every type parameter must be replaced by
      * its (DJS) parent or the concrete type if known.
      */
    def trace( v : MinimalCellT, map : M, xmap: X ) : State[cleanupState, MinimalCellT] =
      v match {
        case x : TypeParam => for {
          p <- internalFindCleanup( x )
          ret <- xmap.getOrElse( p, List( p ) ) map {
            follow( _, map )
          } match {
            case head :: Nil => head.point[CS]
            case lst =>  lst.tail.foldLeft( Option( lst.head ) ) { case (a, b) =>
                a flatMap { t => unify( t, b ) }
              } match {
              case None => setDeadBranch( true ) map { _ => p }
              case Some( e ) => e.point[CS]
            }
          }
        } yield ret
        // Recurse on FunT
        case FunT( a : MinimalCellT, b : MinimalCellT ) => for {
          v1 <- trace( a, map, xmap )
          v2 <- trace( b, map, xmap )
        } yield FunT( v1, v2 )
        // ... and FinSetT
        case FinSetT( x : MinimalCellT ) =>
          trace( x, map, xmap ) map FinSetT
        case IntT() | BoolT() | ConstT() =>
          State[cleanupState, MinimalCellT] { s => (s, v) }
        // Records also recurse on the fields
        case RecordT( mp ) =>
          mp.toList traverseS {
            case (k, w) => trace( w.asInstanceOf[MinimalCellT], map, xmap ) map {
              k -> _
            }
          } map { l => RecordT( SortedMap( l : _* ) ) }
        case XOR( a, b ) => for {
          _ <- setDeadBranch(false)
          v1 <- trace( a, map, xmap )
          deadBranchLeft <- gets[cleanupState, Boolean] { _.deadBranch }
          _ <- setDeadBranch(false)
          v2 <- trace( b, map, xmap )
          deadBranchRight <- gets[cleanupState, Boolean] { _.deadBranch }
        } yield (deadBranchLeft,deadBranchRight) match {
          case (false, false) => XOR (v1, v2)
          case (true, false) =>
            println( s"Type ${a} is inconsistent." )
            v2
          case (false, true) =>
            println( s"Type ${b} is inconsistent." )
            v1
          case (true, true) =>
            throw new TypeException( s"Types ${a} and ${b} are both inconsistent." )
        }
        case _ =>
          throw new InternalCheckerError( s"trace for [${v}] is not implemented" )
      }

    // Call trace on all
    def expand( map : M, djs : D, xmap: X ) : M = {
      val cmp = for {
        baseMap <- map.toList traverseS {
          case (k, v) => trace( v, map, xmap ) map {
            k -> _
          }
        } map {
          _.toMap
        }
        elems <- get[cleanupState] map {
          _.d.elements
        }
        completeMap <- elems.toList traverseS { el : TypeParam =>
          internalFindCleanup( el ) map { p => el -> baseMap.getOrElse( p, p ) }
        }
      } yield completeMap

      cmp.run( cleanupState( djs, deadBranch = false) )._2.toMap
    }

    def internalFind( el : TypeParam ) : internalState[TypeParam] = State[MDCX, TypeParam] {
      st =>
        val (newD, e) = st.d.find( el )
        (st.copy( d = newD ), e)
    }

    def internalUnion( el1 : TypeParam, el2 : TypeParam ) : internalState[TypeParam] = State[MDCX, TypeParam] {
      st =>
        val (newD, e) = st.d.union( el1, el2 )
        (st.copy( d = newD ), e)
    }

    def internalInc( ) : internalState[CounterType] = State[MDCX, CounterType] {
      st =>
        (st.copy( c = st.c + 1 ), st.c)
    }

    def internalGOE( el : TypeParam ) : internalState[MinimalCellT] = gets[MDCX, MinimalCellT] {
      st => st.m.getOrElse( el, el )
    }

    def internalUpdate( k : TypeParam, v : MinimalCellT ) : internalState[Unit] = modify[MDCX] {
      st => st.copy( m = st.m + ( k -> v ) )
    }

    def internalXorDep( k: TypeParam, v: TypeParam ) : internalState[Unit] = modify[MDCX] {
      st => st.copy( x = st.x + ( k -> ( v +: st.x.getOrElse( k, List.empty[TypeParam] ) )  ) )
    }

    def split( m: M ) : TypeMaps = {
      val bRegex : Regex = """\.b_(\d+)""".r
      val cRegex : Regex = """\.c_.*""".r
      val vRegex : Regex = """[^\.].*""".r
      val cmp = m.toList traverseS { case (k,v) =>
        k.s match {
          case bRegex(i) =>
            modify[TypeMaps] { tm =>
              tm.copy( uidMap =  tm.uidMap + (UID( i.toInt ) -> v) )
            }
          case cRegex() =>
            modify[TypeMaps] { tm =>
              tm.copy( typeVarMap = tm.typeVarMap + (k -> v) )
            }
          case vRegex() =>
            modify[TypeMaps] { tm =>
              tm.copy( varTypeMap = tm.varTypeMap + (k.s -> v) )
            }
          case _ =>
            throw new InternalCheckerError( s"Type parameter shape unexpected: ${k.s}" )
        }
      }

      cmp.run( TypeMaps( Map.empty, Map.empty, Map.empty ) )._1
    }

  }

  sealed case class TypeMaps( uidMap: Map[UID, MinimalCellT],
                              typeVarMap: Map[TypeParam, MinimalCellT],
                              varTypeMap : Map[String, MinimalCellT] )

  /**
    * Performs type inference on `tlaEx`
    *
    * @param tlaEx
    * @return Maps every (sub)expression (by ID) to its type
    */
  def apply( tlaEx : TlaEx ) : TypeMaps = { //Map[UID, MinimalCellT] = { // to be Map[UID, CellT]

    import Internals._

    /** Start by computing all isType predicates */
    val queue = theta( tlaEx )

    queue foreach println

    def rememberXor( el : MinimalCellT, v : TypeParam ) : internalState[Unit] = el match {
      case x : TypeParam => internalXorDep( x, v )
      case _ => ().point[internalState]
    }

    def cmp( q : List[isType]) : internalState[List[Unit]] =
      q traverseS { el =>
        for {
          _ <- el match {
            /** If type equality is established between two type parameters we need to call union */
            case isType( v1 : TypeParam, v2 : TypeParam ) => for {
              rep1 <- internalFind( v1 )
              rep2 <- internalFind( v2 )
              t1 <- internalGOE( rep1 )
              t2 <- internalGOE( rep2 )

              _ <- unify( t1, t2 ) match {
                case Some( x ) =>
                  for {
                    // If the unification is possible, the type parameters belong to the same DJS set
                    r <- internalUnion( rep1, rep2 )
                    t = x match {
                      // x can only be a type parameter if both t1 and t2 were.
                      // However, there is no way to predict whether the result of type unification, x,
                      // and set union representative, r, are the same element
                      // (in principle, both are arbitrary choices between t1=rep1 and t2=rep2)
                      // In that case, we always take the set union representative as the new type.
                      case _ : TypeParam => r
                      case _ => x
                    }
                    _ <- internalUpdate( r, t )
                  } yield ()
                case None =>
                  throw new TypeException( s"Types ${t1} and ${t2} are incompatible." )
              }
            } yield ()

            /** If one is a type parameter and the other a constant, the constant dominates */
            case isType( v : TypeParam, c ) => for { // c not a typeparam for sure
              rep <- internalFind( v )
              t <- internalGOE( rep )

              _ <- unify( t, c ) match {
                case Some( newT@XOR( a , b ) ) => for {
//                  _ <- println( s"XOR: $rep  $a  $b" ).point[internalState]
                  _ <- rememberXor(a,rep)
                  _ <- rememberXor(b,rep)
                  _ <- internalUpdate( rep, newT )
                } yield()
                case Some( newT ) =>
                  internalUpdate( rep, newT )
                case None =>
                  throw new TypeException( s"Types ${c} and ${t} are incompatible." )
              }
            } yield ()

            /** isType( c, v: TypeParam ) should not be possible */

            case isType( a, b ) => throw new TypeException( s"Types ${a} and ${b} are incompatible." )
          }
        } yield ()
      }

//    val finalCmp: internalState[Unit] = for {
//      q <- preCmp
//      _ <- cmp(q)
//    } yield ()

    val internal( endMap, endDJS, _ , endX) = cmp(queue).run( internal( Map.empty, DisjointSets.empty, 0, Map.empty ) )._1

    val expanded = expand( endMap, endDJS, endX )

    val r = split( expanded )

    r
  }

}
