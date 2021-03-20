package hu.bme.mit.theta.xcfa.passes.xcfapass;

import hu.bme.mit.theta.xcfa.model.XCFA;

public interface XcfaPass {

    XCFA.Builder run(XCFA.Builder builder);

}
