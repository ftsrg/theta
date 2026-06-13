
package hu.bme.mit.theta.frontend.svlib;

import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibLexer;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.xcfa.model.VisualizerKt.toDot;
import static org.junit.jupiter.api.Assertions.*;

class SvLibFrontendTest {
  @Test
  void testParsing() {
    String source = """
        (define-proc foo
          ((x Int))
          ((y Int))
          ((tmp Int))
          body
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

    assertEquals("SvLibXCFA", xcfa.getName());
    assertFalse(procedure.getLocs().isEmpty());
    assertTrue(procedure.getFinalLoc().isPresent());
  }

  @Test
  void safeIfVerificationExampleCreatesBranchingLocation() {
    var xcfa = parseResource("if-simple-safe.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    var hasBranchingLoc =
        procedure.getEdges().stream()
            .collect(
                java.util.stream.Collectors.groupingBy(
                    edge -> edge.getSource(),
                    java.util.stream.Collectors.counting()))
            .values()
            .stream()
            .anyMatch(count -> count >= 2);

    assertTrue(hasBranchingLoc, "Expected if translation to create a branching location");
  }

  @Test
  void unsafeIfVerificationExampleCreatesErrorLocation() {
    var xcfa = parseResource("if-simple-unsafe.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    assertTrue(procedure.getErrorLoc().isPresent());
    assertTrue(procedure.getEdges().stream().anyMatch(edge -> edge.getTarget().getError()));
  }

  @Test
  void translatedIfXcfaCanBeExportedToDot() throws IOException {
    var xcfa = parseResource("if-simple-safe.svlib");
    var dot = toDot(xcfa, null);
    java.nio.file.Files.writeString(
        java.nio.file.Path.of("svlib-if-simple-safe.dot"),
        dot);

    assertTrue(dot.startsWith("digraph G"));
    assertTrue(dot.contains("SvLibXCFA"));
    assertFalse(dot.isBlank());
  }

  @Test
  void translatedIfXcfaCanBeExportedToDot2() throws IOException {
    var xcfa = parseResource("if-assign.svlib");
    var dot = toDot(xcfa, null);
    java.nio.file.Files.writeString(
        java.nio.file.Path.of("svlib-if-assign.dot"),
        dot);

    assertTrue(dot.startsWith("digraph G"));
    assertTrue(dot.contains("SvLibXCFA"));
    assertFalse(dot.isBlank());
  }

  @Test
  void whileLoopCreatesLoopHeadAndBackEdge()throws IOException {
    var xcfa = parseResource("loop-simple-safe.svlib");
    var procedure = xcfa.getProcedures().iterator().next();

    var incomingCounts =
        procedure.getEdges().stream()
            .collect(Collectors.groupingBy(edge -> edge.getTarget(), Collectors.counting()));
    var outgoingCounts =
        procedure.getEdges().stream()
            .collect(Collectors.groupingBy(edge -> edge.getSource(), Collectors.counting()));

    var dot = toDot(xcfa, null);
    java.nio.file.Files.writeString(
        java.nio.file.Path.of("svlib-loop.dot"),
        dot);

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
