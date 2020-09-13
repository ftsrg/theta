package hu.bme.mit.theta.mcm.dsl;

import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslLexer;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslParser;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.IOException;
import java.io.InputStream;

public class McmDslManager {

    public static MCM createMCM(InputStream inputStream) throws IOException {
        final CharStream input = CharStreams.fromStream(inputStream);

        final McmDslLexer lexer = new McmDslLexer(input);
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        final McmDslParser parser = new McmDslParser(tokens);

        final McmDslParser.SpecificationContext context = parser.specification();
        McmParserVisitor mcmVisitor = new McmParserVisitor();
        context.accept(mcmVisitor);
        return mcmVisitor.getMcm();
    }
}
