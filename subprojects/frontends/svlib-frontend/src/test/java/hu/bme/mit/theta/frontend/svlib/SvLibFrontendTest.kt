package hu.bme.mit.theta.frontend.svlib

import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibLexer
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import java.io.FileInputStream
import java.nio.file.Path

internal class SvLibFrontendTest {

  @Test
  fun testParsing() {
    val source = """
        (define-proc foo
          ((x Int))
          ((y Int))
          ((tmp Int))
          (sequence)
        )
        
        """.trimIndent()

    val parser = SvLibParser(CommonTokenStream(SvLibLexer(CharStreams.fromString(source))))
    val tree = parser.script()
    assertNotNull(tree)
  }

  @Test
  fun safeIfVerificationExampleIsTranslatedToXCFA() {
    val xcfa: XCFA = parseResource("if-simple-safe.svlib")
    val procedure = xcfa.procedures.first()

    assertTrue(procedure.locs.isNotEmpty())
    assertTrue(procedure.finalLoc.isPresent)
  }

  @Test
  fun safeIfVerificationExampleCreatesBranchingLocation() {
    val xcfa: XCFA = parseResource("if-simple-safe.svlib")
    val procedure = xcfa.procedures.first()

    val branchingLocCount = procedure.edges
      .groupBy(XcfaEdge::source)
      .count { (_, edges) -> edges.size >= 2 }

    assertTrue(
      branchingLocCount >= 2,
      "Expected if and check-true translations to create branching locations"
    )
  }

  @Test
  fun unsafeIfVerificationExampleCreatesErrorLocation() {
    val xcfa: XCFA = parseResource("if-simple-unsafe.svlib")
    val procedure = xcfa.procedures.first()

    assertTrue(procedure.errorLoc.isPresent)
    assertTrue(procedure.edges.any { it.target.error })
  }

  @Test
  fun checkTrueCreatesNormalAndErrorBranches() {
    val xcfa: XCFA = parseResource("check-true-middle.svlib")
    val procedure = xcfa.procedures.first()

    val checkLocation = procedure.edges
        .filter { it.target.error }
        .map(XcfaEdge::source)
        .first()

    assertEquals(2, procedure.edges.count { it.source == checkLocation })
  }

  @Test
  fun annotateTagCheckTrueRewritesTaggedLocation() {
    val xcfa: XCFA = parseResource("check-true-annotate-tag.svlib")
    val procedure = xcfa.procedures.first()

    val taggedLocation = procedure.locs.find { loc ->
      loc.metadata.let { metadata ->
        metadata is SvLibTagMetadata && metadata.tags.contains("xto0")
      }
    }

    assertNotNull(taggedLocation)
    assertEquals(2, taggedLocation!!.outgoingEdges.size)
    assertTrue(taggedLocation.outgoingEdges.any { it.target.error })
  }

  @Test
  fun multiAssignStatementCreatesSingleSequenceLabelEdge() {
    val xcfa: XCFA = parseResource("multi-assign.svlib")
    val procedure = xcfa.procedures.first()

    val sequenceLabel = procedure.edges
        .map(XcfaEdge::label)
        .filterIsInstance<SequenceLabel>()
        .first()

    assertEquals(2, sequenceLabel.labels.size)
  }

  @Test
  fun havocStatementCreatesHavocLabel() {
    val xcfa: XCFA = parseResource("havoc.svlib")
    val procedure = xcfa.procedures.first()

    assertTrue(procedure.edges
      .map(XcfaEdge::label)
      .filterIsInstance<StmtLabel>()
      .any { it.stmt is HavocStmt<*> }
    )
  }

  @Test
  fun returnStatementCreatesFinalLocationEdge() {
    val xcfa: XCFA = parseResource("return.svlib")
    val procedure = xcfa.procedures.first()
    val finalLoc = procedure.finalLoc.orElseThrow()

    assertTrue(procedure.edges.any { edge -> edge.target == finalLoc })
  }

  @Test
  fun ifWithReturningBranchContinuesOnlyFromOtherBranch() {
    val xcfa: XCFA = parseResource("return-if.svlib")
    val procedure = xcfa.procedures.first()
    val finalLoc = procedure.finalLoc.orElseThrow()

    assertEquals(2, procedure.edges.count { it.target == finalLoc })
  }

  @Test
  fun whileBodyReturnDoesNotCreateBackEdge() {
    val xcfa: XCFA = parseResource("return-while.svlib")
    val procedure = xcfa.procedures.first()
    val finalLoc = procedure.finalLoc.orElseThrow()

    assertEquals(2, procedure.edges.count { it.target == finalLoc })
    assertTrue(procedure.locs.any { loc ->
      loc.incomingEdges.size >= 2 && loc.outgoingEdges.any { it.label.toString().contains("(< x 3)") }
    })
    assertTrue(procedure.edges
      .filter { it.target == finalLoc && it.label.toString().contains("Nop") }
      .map(XcfaEdge::source)
      .any { it.outgoingEdges.size == 1 }
    )
  }

  @Test
  fun whileLoopCreatesLoopHeadAndBackEdge() {
    val xcfa: XCFA = parseResource("loop-simple-safe.svlib")
    val procedure = xcfa.procedures.first()

    val incomingCounts = procedure.edges.groupBy(XcfaEdge::target).mapValues { (_, edges) -> edges.size }
    val outgoingCounts = procedure.edges.groupBy(XcfaEdge::source).mapValues { (_, edges) -> edges.size }

    assertTrue(procedure.locs.any { loc -> (incomingCounts[loc] ?: 0) >= 2 && (outgoingCounts[loc] ?: 0) >= 2 })
  }

  private fun parseResource(name: String) =
    try {
      val resource = SvLibFrontendTest::class.java.getClassLoader().getResource(name)
      val file = Path.of(resource!!.toURI()).toFile()
      SvLibFrontend(ConsoleLogger(Logger.Level.INFO)).buildXcfa(FileInputStream(file))
    } catch (e: Exception) {
      throw RuntimeException("Failed to parse test resource: $name", e)
    }
}
