package at.forsyte.apalache.tla.types

/**
  * An exception related to a type error. Note that such an exception should be rarely used.
  * Instead errors and warning should be reported with TypeError and TypeWarn.
  *
  * @param message error message
  *
  * @author Igor Konnov
  */
class TypeException(message: String) extends Exception(message)
