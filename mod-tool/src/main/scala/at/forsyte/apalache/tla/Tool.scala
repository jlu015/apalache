package at.forsyte.apalache.tla

import java.time.LocalDateTime
import java.time.temporal.ChronoUnit

import at.forsyte.apalache.infra.PassOptionException
import at.forsyte.apalache.infra.passes.{PassChainExecutor, TlaModuleMixin}
import at.forsyte.apalache.tla.bmcmt.{CheckerException, InternalCheckerError}
import at.forsyte.apalache.tla.bmcmt.passes.CheckerModule
import at.forsyte.apalache.tla.imp.passes.ParserModule
import at.forsyte.apalache.tla.tooling.Version
import at.forsyte.apalache.tla.tooling.opt.{CheckCmd, ParseCmd}
import com.google.inject.Guice
import com.typesafe.scalalogging.LazyLogging
import org.backuity.clist.Cli

/**
  * Command line access to the APALACHE tools.
  *
  * @author Igor Konnov
  */
object Tool extends App with LazyLogging {
  private lazy val ISSUES_LINK: String = "[https://github.com/konnov/apalache/issues]"

  override def main(args: Array[String]): Unit = {
    Console.println("# APALACHE %s".format(Version.version))
    Console.println("#")
    Console.println("# WARNING: This tool is in its early development stage.")
    Console.println("#          Please report bugs at: " + ISSUES_LINK)
    Console.println("")
    val startTime = LocalDateTime.now()
    val parseCmd = new ParseCmd
    val checkCmd = new CheckCmd
    try {
      Cli.parse(args).withProgramName("apalache-mc").version(Version.version)
        .withCommands(parseCmd, checkCmd) match {
        case Some(parse: ParseCmd) =>
          logger.debug("Parse " + parse.file)
          handleExceptions(runParse(parse, _))

        case Some(check: CheckCmd) =>
          logger.info("Checker options: filename=%s, init=%s, next=%s, inv=%s"
            .format(check.file, check.init, check.next, check.inv))
          handleExceptions(runCheck(check, _))

        case _ => () // nothing to do
      }
    } finally {
      printTimeDiff(startTime)
    }
  }

  private def printTimeDiff(startTime: LocalDateTime): Unit = {
    val endTime = LocalDateTime.now()
    Console.println("It took me %d days %2d hours %2d min %2d sec"
      .format(ChronoUnit.DAYS.between(startTime, endTime),
        ChronoUnit.HOURS.between(startTime, endTime) % 23,
        ChronoUnit.MINUTES.between(startTime, endTime) % 60,
        ChronoUnit.SECONDS.between(startTime, endTime) % 60))
    Console.println("Total time: %d.%d sec"
      .format(ChronoUnit.SECONDS.between(startTime, endTime),
        ChronoUnit.MILLIS.between(startTime, endTime) % 1000))
  }

  private def runParse(parse: ParseCmd, u: Unit): Unit = {
    // here, we implement a terminal pass to get the parse results
    val injector = Guice.createInjector(new ParserModule())
    val executor = injector.getInstance(classOf[PassChainExecutor])
    executor.options.setOption("parser.filename", parse.file.getAbsolutePath)

    val result = executor.run()
    if (result.isDefined) {
      logger.info("Parsed successfully")
      val tlaModule = result.get.asInstanceOf[TlaModuleMixin].tlaModule.get
      logger.info("Root module: %s with %d declarations".format(tlaModule.name,
        tlaModule.declarations.length))
    } else {
      logger.error("Parser has failed")
    }
  }

  private def runCheck(check: CheckCmd, u: Unit): Unit = {
    val injector = Guice.createInjector(new CheckerModule())
    val executor = injector.getInstance(classOf[PassChainExecutor])
    executor.options.setOption("general.debug", check.debug)
    executor.options.setOption("smt.prof", check.smtprof)
    executor.options.setOption("parser.filename", check.file.getAbsolutePath)
    executor.options.setOption("checker.init", check.init)
    executor.options.setOption("checker.next", check.next)
    executor.options.setOption("checker.inv",
      if (check.inv != "") Some(check.inv) else None)
    executor.options.setOption("checker.length", check.length)
    executor.options.setOption("checker.search", check.search)
    executor.options.setOption("checker.filter", check.filter)
    executor.options.setOption("checker.checkRuntime", check.checkRuntime)

    val result = executor.run()
    if (result.isDefined) {
      logger.info("Checker reports no error up to computation length " + check.length)
    } else {
      logger.error("Checker has failed")
    }
  }

  private def handleExceptions(fun: Unit => Unit): Unit = {
    try {
      fun()
    } catch {
      case e: PassOptionException =>
        logger.error(e.getMessage)

      case e: InternalCheckerError =>
        logger.error("There is a bug in the tool, which should be fixed. REPORT IT: " + ISSUES_LINK, e)

      case e: CheckerException =>
        logger.error("The tool has failed around unknown location. REPORT IT: " + ISSUES_LINK, e)

      case e: Throwable =>
        logger.error("This should not have happened, but it did. REPORT IT: " + ISSUES_LINK, e)
    }
  }
}
