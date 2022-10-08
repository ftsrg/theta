package hu.bme.mit.theta.frontend.chc;

import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.xcfa.model.XCFA;

public interface ChcXcfaBuilder {
    XCFA.Builder buildXcfa(CHCParser parser);
}
