package hu.bme.mit.theta.frontend.svlib;

import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibLexer;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;

public class SvLibFrontend{

    public static SvLibParser.ScriptContext parse(String source) {
        // 1. source String -> ANTLR CharStream
        CharStream input = CharStreams.fromString(source);

        // 2. CharStream -> Lexer
        SvLibLexer lexer = new SvLibLexer(input);

        // 3. Lexer -> Token stream
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // 4. Token stream -> Parser
        SvLibParser parser = new SvLibParser(tokens);
        parser.setErrorHandler(new BailErrorStrategy());

        // 5. Parser -> Parse tree
        return parser.script();
    }

    private SvLibParser createParser(String source) {
        SvLibLexer lexer = new SvLibLexer(CharStreams.fromString(source));
        SvLibParser parser = new SvLibParser(new CommonTokenStream(lexer));
        parser.setErrorHandler(new BailErrorStrategy());
        return parser;
    }
}