package hu.bme.mit.theta.frontend.chc;

import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCLexer;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.xcfa.model.XCFA;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;

public class ChcFrontend {
    public static ChcTransformation chcTransformation = ChcTransformation.FORWARD;

    public enum ChcTransformation {
        FORWARD,
        BACKWARD
    }

    public XCFA.Builder buildXcfa(CharStream charStream) {
        CHCParser parser = new CHCParser(new CommonTokenStream(new CHCLexer(charStream)));
        ChcXcfaBuilder chcXcfaBuilder = switch (chcTransformation) {
            case FORWARD -> new ChcForwardXcfaBuilder();
            case BACKWARD -> new ChcBackwardXcfaBuilder();
        };
        return chcXcfaBuilder.buildXcfa(parser);
    }
}

