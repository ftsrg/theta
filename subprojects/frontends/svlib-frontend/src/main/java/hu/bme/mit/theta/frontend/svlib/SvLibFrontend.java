package hu.bme.mit.theta.frontend.svlib;

import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager;
import org.antlr.v4.runtime.*;

import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibLexer;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

import static java.util.Objects.requireNonNull;

public class SvLibFrontend{

    private final ProcedurePassManager procedurePassManager;

    public SvLibFrontend() {
        this(new ProcedurePassManager());
    }

    public SvLibFrontend(ProcedurePassManager procedurePassManager) {
        this.procedurePassManager = requireNonNull(procedurePassManager);
    }

    public XCFA buildXcfa(File input) {
        try {
            return buildXcfa(Files.readString(input.toPath()));
        } catch (IOException e) {
            throw new IllegalStateException("Failed to read SV-LIB input from " + input, e);
        }
    }

    public XCFA buildXcfa(String source) {
        SvLibParser parser = createParser(source);
        SvLibParser.ScriptContext script = parser.script();
        return new SvLibXcfaBuilder(procedurePassManager).buildXcfa(script);
    }

    private SvLibParser createParser(String source) {
        SvLibLexer lexer = new SvLibLexer(CharStreams.fromString(source));
        SvLibParser parser = new SvLibParser(new CommonTokenStream(lexer));
        parser.setErrorHandler(new BailErrorStrategy());
        return parser;
    }

}