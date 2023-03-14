package hu.bme.mit.theta.frontend.chc;

import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCLexer;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.xcfa.model.XCFA;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;

public class ChcFrontend {
    public enum ChcTransformation {
        FORWARD,
        BACKWARD
    }

    private final ChcTransformation chcTransformation;

    public ChcFrontend(ChcTransformation transformation) {
        chcTransformation = transformation;
    }

    public XCFA.Builder buildXcfa(CharStream charStream) {
        ChcUtils.init(charStream);
        CHCParser parser = new CHCParser(new CommonTokenStream(new CHCLexer(charStream)));
        ChcXcfaBuilder chcXcfaBuilder = switch (chcTransformation) {
            case FORWARD -> new ChcForwardXcfaBuilder();
            case BACKWARD -> new ChcBackwardXcfaBuilder();
        };
        return chcXcfaBuilder.buildXcfa(parser);
    }
}

