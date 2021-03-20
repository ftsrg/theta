package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

public interface ProcedurePass {

    XcfaProcedure.Builder run(XcfaProcedure.Builder builder);

}
