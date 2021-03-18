package hu.bme.mit.theta.xcfa.ir.passes;

import hu.bme.mit.theta.xcfa.XCFA;

public interface ProcedurePass {

    XCFA.Process.Procedure.Builder run(XCFA.Process.Procedure.Builder builder);

}
