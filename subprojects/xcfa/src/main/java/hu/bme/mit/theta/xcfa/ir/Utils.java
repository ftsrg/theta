package hu.bme.mit.theta.xcfa.ir;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;
import java.util.List;

public class Utils {
    public static VarDecl<?> createVariable(String name, IRType IRType) {
        return null; //TODO
    }

    public static LitExpr<?> createConstant(IRType IRType, String value) {
        return null; //TODO
    }

    public static Collection<String> handleProcedure(Tuple3<String, IRType, List<Tuple2<IRType, String>>> function, XCFA.Process.Procedure.Builder procedureBuilder) {
        return null; // TODO
    }

}
