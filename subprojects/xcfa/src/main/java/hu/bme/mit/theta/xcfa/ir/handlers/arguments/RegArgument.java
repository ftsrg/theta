package hu.bme.mit.theta.xcfa.ir.handlers.arguments;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.util.Map;

import static hu.bme.mit.theta.xcfa.ir.Utils.createType;

public class RegArgument extends Argument{
    private final String name;
    private final Type type;

    RegArgument(String type, String name) {
        this.name = name;
        this.type = createType(type);
    }

    @Override
    public Type getType() {
        return type;
    }

    @Override
    public Expr<?> getExpr(Map<String, Expr<?>> values) {
        return values.get(name);
    }

    @Override
    public String getName() {
        return name;
    }
}
