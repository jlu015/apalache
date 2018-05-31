package at.forsyte.apalache.tla.types.tsa

import at.forsyte.apalache.tla.lir.UID
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.plugins.Identifier
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.collection.mutable


@RunWith(classOf[JUnitRunner])
class TestTypeInferer extends FunSuite {
  test("infer integer") {
    val typeMap = mutable.Map[UID, CellT]()
    val infer = new TypeInferer(typeMap)

    val e = tla.int(81)
    Identifier.identify(e)
    infer.inferRecAndStore(e)
    assert(IntT() == typeMap(e.uid))
  }
}
