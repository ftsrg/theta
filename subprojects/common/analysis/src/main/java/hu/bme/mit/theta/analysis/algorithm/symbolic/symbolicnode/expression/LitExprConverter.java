package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.math.BigInteger;

/**
 * Util class for converting between integers and {@link LitExpr}
 */
public class LitExprConverter {

    public static int toInt(LitExpr<?> litExpr) {
        if (litExpr instanceof IntLitExpr) {
            return ((IntLitExpr) litExpr).getValue().intValue();
        }
        if (litExpr instanceof BoolLitExpr) {
            return ((BoolLitExpr) litExpr).getValue() ? 1 : 0;
        }
        throw new UnsupportedOperationException("Unsupported type");
    }

    public static LitExpr<?> toLitExpr(int integer, Type type) {
        if (type instanceof IntType) {
            return IntLitExpr.of(BigInteger.valueOf(integer));
        }
        if (type instanceof BoolType) {
            return BoolLitExpr.of(integer != 0);
        }
        throw new UnsupportedOperationException("Unsupported type");
    }

}
