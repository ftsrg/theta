package hu.bme.mit.theta.xcfa.ir.passes;

import hu.bme.mit.theta.xcfa.XcfaProcedure;

public interface ProcedurePass {

    XcfaProcedure.Builder run(XcfaProcedure.Builder builder);

}
