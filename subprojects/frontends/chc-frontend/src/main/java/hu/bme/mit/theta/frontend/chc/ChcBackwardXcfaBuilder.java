package hu.bme.mit.theta.frontend.chc;

import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCBaseVisitor;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.xcfa.model.XCFA;

public class ChcBackwardXcfaBuilder extends CHCBaseVisitor<Object> implements ChcXcfaBuilder {
    @Override
    public XCFA.Builder buildXcfa(CHCParser parser) {
        throw new UnsupportedOperationException("Backwards transformation is not implemented yet."); // TODO
    }
}
