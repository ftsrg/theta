package hu.bme.mit.theta.xcfa.ir.handlers.arguments;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.math.BigInteger;
import java.util.Map;

public class ConstantArgument extends Argument{
    private final LitExpr<?> expr;

    ConstantArgument(String type, String name) {
        switch(type) {
            case "i32":
            case "i16":
            case "i8":
                this.expr = IntLitExpr.of(new BigInteger(name)); break;
            case "i1": this.expr = BoolLitExpr.of(name.equals("true")); break;
            default: throw new RuntimeException("Type " + type + " not known!");
        }
    }

    @Override
    public Type getType() {
        return expr.getType();
    }

    @Override
    public Expr<?> getExpr(Map<String, Expr<?>> values) {
        return expr;
    }

    @Override
    public String getName() {
        return expr.toString();
    }
}
