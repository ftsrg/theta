package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GeneralResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Assert;
import org.junit.Test;

public class SmtLibParserTest {
    @Test
    public void ambiguousParsingTest() {

        final var response = "(\n)";

        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(response));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        var general = GeneralResponse.fromContext(parser.response());
        Assert.assertTrue(general.isSpecific());

        Assert.assertTrue(general.asSpecific().isGetUnsatCoreResponse());
        Assert.assertEquals(0, general.asSpecific().asGetUnsatCoreResponse().getLabels().size());

        Assert.assertTrue(general.asSpecific().isGetModelResponse());
        Assert.assertEquals(0, general.asSpecific().asGetModelResponse().getModel().size());
    }
}
