package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.UID

/**
  * A warning registered at a type inference phase. This is what we consider strange behavior,
  * although not silly. For instance, there is a clear interpretation for 1 \ne FALSE,
  * but writing this expression was probably not the user intention.
  *
  * @param exprId the id of a problematic expression
  * @param message a warning message
  *
  * @author konnov
  */
class TypeWarn(val exprId: UID, val message: String)


object TypeWarn {
  def apply(exprId: UID, message: String): TypeWarn = {
    new TypeWarn(exprId, message)
  }
}
