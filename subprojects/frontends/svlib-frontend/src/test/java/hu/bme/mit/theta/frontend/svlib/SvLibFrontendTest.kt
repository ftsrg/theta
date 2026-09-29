
package hu.bme.mit.theta.frontend.svlib;

import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibLexer;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;
import hu.bme.mit.theta.xcfa.model.SequenceLabel;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.Test;

import java.nio.file.Path;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.*;

class SvLibFrontendTest {
  @Test
  void testParsing() {
    String source = """
        (define-proc foo
          ((x Int))
          ((y Int))
          ((tmp Int))
          (sequence)
        )
        """;

    SvLibParser parser = new SvLibParser(
        new CommonTokenStream(
            new SvLibLexer(CharStreams.fromString(source))
        )
    );

    SvLibParser.ScriptContext tree =
        assertDoesNotThrow(parser::script);

    System.out.println(tree.toStringTree(parser));

    assertNotNull(tree);
  }

  @Test
  void safeIfVerificationExampleIsTranslatedToXCFA() {
    var xcfa = parseResource("if-simple-safe.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    assertFalse(procedure.getLocs().isEmpty());
    assertTrue(procedure.getFinalLoc().isPresent());
  }

  @Test
  void safeIfVerificationExampleCreatesBranchingLocation() {
    var xcfa = parseResource("if-simple-safe.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    var branchingLocCount =
        procedure.getEdges().stream()
            .collect(
                java.util.stream.Collectors.groupingBy(
                    edge -> edge.getSource(),
                    java.util.stream.Collectors.counting()))
            .values()
            .stream()
            .filter(count -> count >= 2)
            .count();

    assertTrue(
        branchingLocCount >= 2,
        "Expected if and check-true translations to create branching locations");
  }

  @Test
  void unsafeIfVerificationExampleCreatesErrorLocation() {
    var xcfa = parseResource("if-simple-unsafe.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    assertTrue(procedure.getErrorLoc().isPresent());
    assertTrue(procedure.getEdges().stream().anyMatch(edge -> edge.getTarget().getError()));
  }

  @Test
  void checkTrueCreatesNormalAndErrorBranches() {
    var xcfa = parseResource("check-true-middle.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    var checkLocation =
        procedure.getEdges().stream()
            .filter(edge -> edge.getTarget().getError())
            .map(edge -> edge.getSource())
            .findFirst()
            .orElseThrow();

    assertEquals(
        2,
        procedure.getEdges().stream()
            .filter(edge -> edge.getSource().equals(checkLocation))
            .count());
  }

  @Test
  void annotateTagCheckTrueRewritesTaggedLocation() {
    var xcfa = parseResource("check-true-annotate-tag.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    var taggedLocation =
        procedure.getLocs().stream()
            .filter(
                loc ->
                    loc.getMetadata() instanceof SvLibMetadata metadata
                        && metadata.isTag()
                        && metadata.getTag().equals("xto0"))
            .findFirst()
            .orElseThrow();

    assertEquals(2, taggedLocation.getOutgoingEdges().size());
    assertTrue(taggedLocation.getOutgoingEdges().stream().anyMatch(edge -> edge.getTarget().getError()));
  }

  @Test
  void multiAssignStatementCreatesSingleSequenceLabelEdge() {
    var xcfa = parseResource("multi-assign.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    var sequenceLabel =
        procedure.getEdges().stream()
            .map(edge -> edge.getLabel())
            .filter(SequenceLabel.class::isInstance)
            .map(SequenceLabel.class::cast)
            .findFirst()
            .orElseThrow();

    assertEquals(2, sequenceLabel.getLabels().size());
  }

  @Test
  void havocStatementCreatesHavocLabel() {
    var xcfa = parseResource("havoc.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    assertTrue(
        procedure.getEdges().stream()
            .map(edge -> edge.getLabel())
            .filter(StmtLabel.class::isInstance)
            .map(StmtLabel.class::cast)
            .anyMatch(label -> label.getStmt() instanceof HavocStmt<?>));
  }

  @Test
  void returnStatementCreatesFinalLocationEdge() {
    var xcfa = parseResource("return.svlib");
    var procedure = xcfa.getProcedures().iterator().next();
    var finalLoc = procedure.getFinalLoc().orElseThrow();

    assertTrue(
        procedure.getEdges().stream()
            .anyMatch(
                edge ->
                    edge.getTarget().equals(finalLoc)
                        && edge.getSource().getMetadata() instanceof SvLibMetadata metadata
                        && metadata.getSourceName().equals("assign")));
  }

  @Test
  void ifWithReturningBranchContinuesOnlyFromOtherBranch() {
    var xcfa = parseResource("return-if.svlib");
    var procedure = xcfa.getProcedures().iterator().next();
    var finalLoc = procedure.getFinalLoc().orElseThrow();

    assertEquals(
        2,
        procedure.getEdges().stream()
            .filter(edge -> edge.getTarget().equals(finalLoc))
            .count());
  }

  @Test
  void whileBodyReturnDoesNotCreateBackEdge() {
    var xcfa = parseResource("return-while.svlib");
    var procedure = xcfa.getProcedures().iterator().next();
    var finalLoc = procedure.getFinalLoc().orElseThrow();

    assertEquals(
        2,
        procedure.getEdges().stream()
            .filter(edge -> edge.getTarget().equals(finalLoc))
            .count());
    assertTrue(
        procedure.getLocs().stream()
            .anyMatch(
                loc ->
                    loc.getIncomingEdges().size() >= 2
                        && loc.getOutgoingEdges().stream()
                            .anyMatch(edge -> edge.getLabel().toString().contains("(< x 3)"))));
    assertTrue(
        procedure.getEdges().stream()
            .filter(edge -> edge.getTarget().equals(finalLoc))
            .filter(edge -> edge.getLabel().toString().contains("Nop"))
            .map(edge -> edge.getSource())
            .anyMatch(source -> source.getOutgoingEdges().size() == 1));
  }

  @Test
  void whileLoopCreatesLoopHeadAndBackEdge() {
    var xcfa = parseResource("loop-simple-safe.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    var incomingCounts =
        procedure.getEdges().stream()
            .collect(Collectors.groupingBy(edge -> edge.getTarget(), Collectors.counting()));
    var outgoingCounts =
        procedure.getEdges().stream()
            .collect(Collectors.groupingBy(edge -> edge.getSource(), Collectors.counting()));

    assertTrue(
        procedure.getLocs().stream()
            .anyMatch(
                loc ->
                    incomingCounts.getOrDefault(loc, 0L) >= 2
                        && outgoingCounts.getOrDefault(loc, 0L) >= 2));


  }

  private static hu.bme.mit.theta.xcfa.model.XCFA parseResource(String name) {
    try {
      var resource = SvLibFrontendTest.class.getClassLoader().getResource(name);

      assertNotNull(resource, "Test resource not found: " + name);

      var file = Path.of(resource.toURI()).toFile();
      assertTrue(file.exists(), "Test resource file does not exist: " + file);

      return new SvLibFrontend().buildXcfa(file);
    } catch (Exception e) {
      throw new RuntimeException("Failed to parse test resource: " + name, e);
    }
  }

}
