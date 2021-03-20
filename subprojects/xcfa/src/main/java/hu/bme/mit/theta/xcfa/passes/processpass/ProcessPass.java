package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.xcfa.model.XcfaProcess;

public interface ProcessPass {

    XcfaProcess.Builder run(XcfaProcess.Builder builder);


}
