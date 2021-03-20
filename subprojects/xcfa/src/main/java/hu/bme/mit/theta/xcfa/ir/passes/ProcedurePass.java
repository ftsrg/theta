package hu.bme.mit.theta.xcfa.ir.passes;

import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

public interface ProcedurePass {

    XcfaProcedure.Builder run(XcfaProcedure.Builder builder);

}
