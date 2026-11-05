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

import static hu.bme.mit.theta.core.type.fptype.FpExprs.MathFunc;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.fptype.FpMathFuncExpr.Function;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import java.util.List;
import java.util.Map;
import java.util.function.DoubleUnaryOperator;
import org.junit.jupiter.api.Test;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

public class FpMathFuncExprTest {

    private static final FpType DOUBLE = FpType.of(11, 53);

    private static FpLitExpr d(final double value) {
        return FpUtils.bigFloatToFpLitExpr(
                new BigFloat(value, new BinaryMathContext(53, 11)), DOUBLE);
    }

    private static final FpLitExpr POS_ZERO = FpExprs.PositiveZero(DOUBLE);
    private static final FpLitExpr NEG_ZERO = FpExprs.NegativeZero(DOUBLE);
    private static final FpLitExpr POS_INF = FpExprs.PositiveInfinity(DOUBLE);
    private static final FpLitExpr NEG_INF = FpExprs.NegativeInfinity(DOUBLE);
    private static final FpLitExpr NAN = FpExprs.NaN(DOUBLE);

    private static FpLitExpr special(final Function f, final FpLitExpr x) {
        return f.specialValue(x).orElseThrow();
    }

    @Test
    public void specialValuesFollowAnnexF() {
        assertEquals(d(1), special(Function.EXP, POS_ZERO));
        assertEquals(d(1), special(Function.EXP, NEG_ZERO));
        assertEquals(POS_ZERO, special(Function.EXP, NEG_INF));
        assertEquals(NEG_ZERO, special(Function.EXPM1, NEG_ZERO));
        assertEquals(d(-1), special(Function.EXPM1, NEG_INF));
        assertEquals(NEG_INF, special(Function.LOG, NEG_ZERO));
        assertEquals(POS_ZERO, special(Function.LOG, d(1)));
        assertTrue(special(Function.LOG, d(-1)).isNaN());
        assertTrue(special(Function.LOG, NEG_INF).isNaN());
        assertEquals(NEG_INF, special(Function.LOG1P, d(-1)));
        assertTrue(special(Function.LOG1P, d(-2)).isNaN());
        assertEquals(NEG_ZERO, special(Function.SIN, NEG_ZERO));
        assertTrue(special(Function.SIN, POS_INF).isNaN());
        assertEquals(d(1), special(Function.COS, NEG_ZERO));
        assertEquals(d(-1), special(Function.TANH, NEG_INF));
        assertEquals(d(1), special(Function.ERF, POS_INF));
        assertEquals(POS_ZERO, special(Function.ACOS, d(1)));
        assertTrue(special(Function.ACOS, d(1.5)).isNaN());
        assertEquals(NEG_ZERO, special(Function.ASIN, NEG_ZERO));
        assertTrue(special(Function.ASIN, NEG_INF).isNaN());
        assertEquals(POS_INF, special(Function.ATANH, d(1)));
        assertEquals(NEG_INF, special(Function.ATANH, d(-1)));
        assertTrue(special(Function.ATANH, d(2)).isNaN());
        for (final Function f : Function.values()) {
            assertTrue(special(f, NAN).isNaN(), f.getLabel());
        }
    }

    @Test
    public void ordinaryInputsHaveNoValue() {
        for (final Function f : Function.values()) {
            assertTrue(f.specialValue(d(0.5)).isEmpty(), f.getLabel());
            final var app = MathFunc(f, d(0.5));
            assertThrows(
                    UnsupportedOperationException.class,
                    () -> app.eval(ImmutableValuation.empty()));
            assertEquals(app, ExprUtils.simplify(app));
        }
    }

    @Test
    public void simplifierFoldsOnlySpecialValues() {
        assertEquals(d(1), ExprUtils.simplify(MathFunc(Function.EXP, POS_ZERO)));
        assertEquals(NEG_ZERO, ExprUtils.simplify(MathFunc(Function.TANH, NEG_ZERO)));
    }

    private static boolean holds(final List<Expr<BoolType>> facts) {
        return facts.stream()
                .allMatch(e -> ((BoolLitExpr) e.eval(ImmutableValuation.empty())).getValue());
    }

    @Test
    public void factsAgreeWithSpecialValues() {
        final List<FpLitExpr> inputs =
                List.of(POS_ZERO, NEG_ZERO, POS_INF, NEG_INF, NAN, d(1), d(-1), d(-2));
        for (final Function f : Function.values()) {
            for (final FpLitExpr x : inputs) {
                f.specialValue(x)
                        .ifPresent(
                                r -> assertTrue(holds(f.facts(x, r)), f.getLabel() + " at " + x));
            }
        }
    }

    /** The bounds must admit what a real libm returns: Java's StrictMath is fdlibm. */
    @Test
    public void factsAdmitFdlibmResults() {
        final Map<Function, DoubleUnaryOperator> libm =
                Map.of(
                        Function.EXP, StrictMath::exp,
                        Function.EXPM1, StrictMath::expm1,
                        Function.LOG, StrictMath::log,
                        Function.LOG1P, StrictMath::log1p,
                        Function.SIN, StrictMath::sin,
                        Function.COS, StrictMath::cos,
                        Function.TANH, StrictMath::tanh,
                        Function.ACOS, StrictMath::acos,
                        Function.ASIN, StrictMath::asin);
        final double[] inputs = {
            -700, -20, -3, -1.5, -1, -0.999, -0.5, -1e-10, 1e-300, 1e-10, 0.5, 0.999, 1, 1.000001,
            3, 20, 700, 1e10
        };
        libm.forEach(
                (f, op) -> {
                    for (final double x : inputs) {
                        final double r = op.applyAsDouble(x);
                        if (Double.isNaN(r) || Double.isInfinite(r)) {
                            continue;
                        }
                        assertTrue(holds(f.facts(d(x), d(r))), f.getLabel() + "(" + x + ")");
                    }
                });
    }

    @Test
    public void factsRejectImpossibleResults() {
        assertTrue(!holds(Function.EXP.facts(d(1), d(-1))));
        assertTrue(!holds(Function.TANH.facts(d(3), d(1.5))));
        assertTrue(!holds(Function.LOG.facts(d(0.5), d(0.1))));
        assertTrue(!holds(Function.SIN.facts(POS_INF, d(0))));
        assertTrue(!holds(Function.ACOS.facts(d(0.5), d(-0.1))));
        assertTrue(!holds(Function.ATANH.facts(d(0.5), d(-0.5))));
    }
}
