package hu.bme.mit.theta.xcfa.ir.passes;

import hu.bme.mit.theta.xcfa.XCFAProcedure;

public interface ProcedurePass {

    XCFAProcedure.Builder run(XCFAProcedure.Builder builder);

}
