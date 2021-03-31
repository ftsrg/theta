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

import static hu.bme.mit.theta.xcfa.ir.Utils.createConstant;

public class ConstantArgument extends Argument{
    private final LitExpr<?> expr;

    ConstantArgument(String type, String name) {
        this.expr = createConstant(type + " " + name);
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
