
package hu.bme.mit.theta.frontend.svlib;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNotNull;

import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibLexer;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.Test;

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

}
