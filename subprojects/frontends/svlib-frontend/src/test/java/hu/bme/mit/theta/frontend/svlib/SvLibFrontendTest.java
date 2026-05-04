
package hu.bme.mit.theta.frontend.svlib;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNotNull;

import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;

import org.junit.jupiter.api.Test;

class SvLibFrontendTest {

    @Test
    void testParsing() {
      String source = """
                (set-logic ALL)
                (declare-fun x () Int)
                """;
      SvLibParser.ScriptContext tree =
          assertDoesNotThrow(() -> SvLibFrontend.parse(source));

      assertNotNull(tree);
    }
}
