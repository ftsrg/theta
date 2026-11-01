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
package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Add;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.NaN;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.NegativeInfinity;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.NegativeZero;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Neq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.PositiveInfinity;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.PositiveZero;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Sub;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import java.util.List;
import org.junit.jupiter.api.Test;

/**
 * The simplifier must preserve IEEE semantics for every value, NaN, infinities and -0.0 included.
 */
public class ExprSimplifierFpTest {

    private static final FpType DOUBLE = FpType.of(11, 53);
    private static final FpRoundingMode RNE = FpRoundingMode.RNE;
    private static final VarDecl<FpType> X = Var("x", DOUBLE);
    private static final VarDecl<FpType> Y = Var("y", DOUBLE);

    private static FpLitExpr lit(double d) {
        return FpUtils.fromString(Double.toString(d), DOUBLE);
    }

    private static List<FpLitExpr> values() {
        return List.of(
                NaN(DOUBLE),
                PositiveInfinity(DOUBLE),
                NegativeInfinity(DOUBLE),
                PositiveZero(DOUBLE),
                NegativeZero(DOUBLE),
                lit(1.0),
                lit(-2.5));
    }

    /** The simplified expression evaluates to the same literal as the original for every x, y. */
    private static <T extends Type> void assertSameValue(Expr<T> expr) {
        final Expr<T> simplified = ExprUtils.simplify(expr);
        for (FpLitExpr x : values()) {
            for (FpLitExpr y : values()) {
                final var val = ImmutableValuation.builder().put(X, x).put(Y, y).build();
                final LitExpr<T> expected = expr.eval(val);
                final LitExpr<T> actual = simplified.eval(val);
                assertEquals(
                        expected,
                        actual,
                        "x=" + x + ", y=" + y + ": " + expr + " simplified to " + simplified);
            }
        }
    }

    @Test
    public void testSelfNeqIsTrueForNaN() {
        assertSameValue(Neq(X.getRef(), X.getRef()));
    }

    @Test
    public void testSelfSubIsNaNForNaNAndInfinity() {
        assertSameValue(Sub(RNE, X.getRef(), X.getRef()));
    }

    @Test
    public void testAddingPositiveZeroIsNotIdentity() {
        assertSameValue(Add(RNE, List.of(X.getRef(), PositiveZero(DOUBLE))));
    }

    @Test
    public void testAdditionIsNotReassociated() {
        assertSameValue(Add(RNE, List.of(Add(RNE, List.of(X.getRef(), lit(1e17))), lit(-1e17))));
        assertSameValue(Add(RNE, List.of(X.getRef(), Add(RNE, List.of(Y.getRef(), lit(1.0))))));
    }

    @Test
    public void testLeadingLiteralsAreFolded() {
        final Expr<FpType> expr = Add(RNE, List.of(lit(1.0), lit(2.0), X.getRef()));
        assertSameValue(expr);
        assertEquals(Add(RNE, List.of(lit(3.0), X.getRef())), ExprUtils.simplify(expr));
        assertEquals(lit(3.0), ExprUtils.simplify(Add(RNE, List.of(lit(1.0), lit(2.0)))));
    }
}
