/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.type.fptype;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;

/**
 * A C math-library function with no counterpart in the SMT-LIB FloatingPoint theory, applied to a
 * floating-point operand of the result's type.
 *
 * <p>Solvers encode it as an uninterpreted function per function and sort, so it is only
 * functionally consistent: equal operands give equal results. It deliberately has no {@link #eval}:
 * a correctly rounded value need not be what the program's libm returns, and folding one would
 * decide a verdict on a value the program may never compute.
 */
public final class FpTranscendentalExpr extends UnaryExpr<FpType, FpType> {

    public enum Function {
        EXP("fpexp"),
        EXPM1("fpexpm1"),
        LOG("fplog"),
        LOG1P("fplog1p"),
        SIN("fpsin"),
        COS("fpcos"),
        TANH("fptanh"),
        ERF("fperf");

        private final String label;

        Function(final String label) {
            this.label = label;
        }

        public String getLabel() {
            return label;
        }

        public static Function fromLabel(final String label) {
            for (final Function f : values()) {
                if (f.label.equals(label)) {
                    return f;
                }
            }
            return null;
        }
    }

    private static final int HASH_SEED = 6672;

    private final Function function;

    private FpTranscendentalExpr(final Function function, final Expr<FpType> op) {
        super(op);
        this.function = checkNotNull(function);
    }

    public static FpTranscendentalExpr of(final Function function, final Expr<FpType> op) {
        return new FpTranscendentalExpr(function, castFp(op));
    }

    public static FpTranscendentalExpr create(final Function function, final Expr<?> op) {
        checkNotNull(op);
        return FpTranscendentalExpr.of(function, castFp(op));
    }

    public Function getFunction() {
        return function;
    }

    @Override
    public FpType getType() {
        return getOp().getType();
    }

    @Override
    public FpLitExpr eval(final Valuation val) {
        throw new UnsupportedOperationException(
                "No exact value for " + function.getLabel() + ": it is left to the solver");
    }

    @Override
    public FpTranscendentalExpr with(final Expr<FpType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return FpTranscendentalExpr.of(function, op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FpTranscendentalExpr that = (FpTranscendentalExpr) obj;
            return this.function == that.function && this.getOp().equals(that.getOp());
        } else {
            return false;
        }
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED + 31 * function.ordinal();
    }

    @Override
    public String getOperatorLabel() {
        return function.getLabel();
    }
}
