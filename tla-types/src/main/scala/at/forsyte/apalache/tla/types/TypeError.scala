package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.UID

/**
  * An error registered at a type inference phase.
  *
  * @param exprId the id of a problematic expression
  * @param message an error message
  *
  * @author konnov
  */
class TypeError(val exprId: UID, val message: String)


object TypeError {
  def apply(exprId: UID, message: String): TypeError = {
    new TypeError(exprId, message)
  }
}