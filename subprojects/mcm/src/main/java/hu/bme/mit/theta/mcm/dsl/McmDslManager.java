package hu.bme.mit.theta.mcm.dsl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslLexer;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslParser;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Process;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;
import java.util.Set;

public class McmDslManager {

    public static MCM createMCM(InputStream inputStream, List<? extends Process> processes, Set<VarDecl<? extends Type>> variables) throws IOException {
        final CharStream input = CharStreams.fromStream(inputStream);

        final McmDslLexer lexer = new McmDslLexer(input);
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        final McmDslParser parser = new McmDslParser(tokens);

        final McmDslParser.SpecificationContext context = parser.specification();
        McmDefinitionParserVisitor mcmVisitor = new McmDefinitionParserVisitor(processes, variables);
        context.accept(mcmVisitor);
        return mcmVisitor.getMcm();
    }
}
