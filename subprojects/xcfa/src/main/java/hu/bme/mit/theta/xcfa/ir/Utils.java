package hu.bme.mit.theta.xcfa.ir;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.math.BigInteger;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

public class Utils {

    public static Type createType(String type) {
        switch(type) {
            case "i32":
            case "i16":
            case "i8":
                return Int();
            case "i1":  return Bool();
            default: throw new RuntimeException("Type " + type + " not known!");
        }
    }

    public static VarDecl<? extends Type> createVariable(String name, String type) {
        Type t = createType(type);
        return Var(name, t);
    }

    public static LitExpr<? extends Type> createConstant(String value) {
        String[] arguments = value.split(" ");
        if(arguments.length != 2) {
            System.err.println("Contant should be of form \"(type=[a-zA-Z0-9]*) (value=[\\.0-9fe+-]*)\", got: " + value);
            return IntLitExpr.of(BigInteger.ZERO);
        }

        switch(arguments[1]) {
            case "true": arguments[1] = "1"; break;
            case "false": arguments[1] = "0"; break;
            default: break;
        }

        if(!arguments[0].startsWith("i")) {
            System.err.println("Unexpected value type: " + arguments[0]);
        }
        return IntLitExpr.of(new BigInteger(arguments[1]));
    }

    public static XcfaProcedure createEmptyProc(String name) {
        XcfaProcedure.Builder builder = XcfaProcedure.builder();
        XcfaLocation loc1 = new XcfaLocation("loc", null);
        XcfaLocation loc2 = new XcfaLocation("loc", null);
        builder.addLoc(loc1);
        builder.addLoc(loc2);
        builder.setFinalLoc(loc2);
        builder.setInitLoc(loc1);
        builder.setName(name);
        return builder.build();
    }

}
