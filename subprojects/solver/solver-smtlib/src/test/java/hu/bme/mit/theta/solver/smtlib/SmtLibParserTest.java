package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.parser.GeneralResponse;
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Assert;
import org.junit.Test;

import java.util.Map;

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

    @Test
    public void letTest() {
        final var response = "" +
            "(let ((a!1 (* (mod 15 4294967296)\n" +
            "              (mod (+ 1 (mod 15 4294967296)) 4294967296))))\n" +
            "(let ((a!2 (* (- 1) (mod (div (mod a!1 4294967296) 2) 4294967296))))\n" +
            "  (= (+ 16 a!2) 0)))";

        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(response));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        final var symbolTable = new GenericSmtLibSymbolTable();
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var expr = termTransformer.toExpr(response, BoolExprs.Bool(), new SmtLibModel(Map.of()));

        Assert.assertNotNull(expr);
    }
}
