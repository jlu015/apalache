package at.forsyte.apalache.tla.types.tsa

import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{TlaEx, UID, ValEx}
import at.forsyte.apalache.tla.types.TypeException

import scala.collection.mutable

class TypeInferer(val typeMap: mutable.Map[UID, CellT]) {
  /**
    * Recursively infer the types of all subexpressions and store them.
    *
    * @param e a TLA+ expression
    * @return the inferred type
    * @throws TypeException if the expression cannot be assigned a sound type.
    */
  def inferRecAndStore(e: TlaEx): CellT = {
    val inferredType = e match {
        case ValEx(TlaInt(_)) => IntT()
        case _ => UnknownT()
      }
    typeMap.put(e.uid, inferredType)
    inferredType
  }
}
