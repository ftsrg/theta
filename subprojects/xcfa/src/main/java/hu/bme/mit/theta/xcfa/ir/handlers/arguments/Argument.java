package hu.bme.mit.theta.xcfa.ir.handlers.arguments;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

import java.util.Map;

import static com.google.common.base.Preconditions.checkState;

public abstract class Argument {

    public abstract Type getType();

    public abstract Expr<?> getExpr(Map<String, Expr<?>> values);

    public abstract String getName();

    public static Argument of(String type, String name) {
        if(!type.equals("")) {
            return new RegArgument(type, name);
        }

        String[] split = name.split(" ");
        if(split.length == 2) {
            switch (split[0]) {
                case "meta":
                    return new StringArgument(null, split[1]);
                case "label":
                    return new LabelArgument(null, split[1]);
                default:
                    return new ConstantArgument(split[0], split[1]);
            }
        }
        else return new StringArgument(null, split[1]);
    }
}
