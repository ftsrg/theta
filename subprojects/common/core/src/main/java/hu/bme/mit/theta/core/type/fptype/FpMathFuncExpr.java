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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Eq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Geq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Gt;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.IsInfinite;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.IsNan;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Leq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Lt;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;

import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.FpUtils;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * A C math-library function with no counterpart in the SMT-LIB FloatingPoint theory, applied to a
 * floating-point operand of the result's type.
 *
 * <p>Solvers encode it as an uninterpreted function per function and sort, so on its own it is only
 * functionally consistent. What is known about it is stated by {@link Function#facts}: the special
 * values of C Annex F (F.10), which are exact, and range bounds by representable values (0, ±1,
 * ±inf), which any faithfully rounded libm preserves. A user of the expression asserts them.
 *
 * <p>{@link #eval} answers only for those special inputs. Any other value is left to the solver: a
 * correctly rounded result need not be what the program's libm returns, and folding one would
 * decide a verdict on a value the program may never compute.
 */
public final class FpMathFuncExpr extends UnaryExpr<FpType, FpType> {

    /** The constants a fact refers to, in the operand's sort. */
    private record Consts(
            FpLitExpr zero,
            FpLitExpr one,
            FpLitExpr minusOne,
            FpLitExpr two,
            FpLitExpr four,
            FpLitExpr posInf,
            FpLitExpr negInf,
            FpLitExpr nan) {
        static Consts of(final FpType type) {
            final FpLitExpr one = FpUtils.fromString("1", type);
            return new Consts(
                    FpExprs.PositiveZero(type),
                    one,
                    one.neg(),
                    FpUtils.fromString("2", type),
                    FpUtils.fromString("4", type),
                    FpExprs.PositiveInfinity(type),
                    FpExprs.NegativeInfinity(type),
                    FpExprs.NaN(type));
        }
    }

    /** Exact result {@code value(x)} wherever {@code guard(x)} holds; the first match applies. */
    private record Case(Expr<BoolType> guard, Expr<FpType> value) {}

    public enum Function {
        EXP("fpmath.exp"),
        EXPM1("fpmath.expm1"),
        LOG("fpmath.log"),
        LOG1P("fpmath.log1p"),
        SIN("fpmath.sin"),
        COS("fpmath.cos"),
        TANH("fpmath.tanh"),
        ERF("fpmath.erf"),
        ACOS("fpmath.acos"),
        ASIN("fpmath.asin"),
        ATANH("fpmath.atanh");

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

        /** The special values; `Eq(x, 0)` is IEEE equality, so it matches both zeros. */
        private List<Case> cases(final Expr<FpType> x, final Consts c) {
            final List<Case> cases = new ArrayList<>();
            cases.add(new Case(IsNan(x), c.nan()));
            switch (this) {
                case EXP -> {
                    cases.add(new Case(Eq(x, c.zero()), c.one()));
                    cases.add(new Case(FpAssign(x, c.negInf()), c.zero()));
                    cases.add(new Case(FpAssign(x, c.posInf()), c.posInf()));
                }
                case EXPM1 -> {
                    cases.add(new Case(Eq(x, c.zero()), x));
                    cases.add(new Case(FpAssign(x, c.negInf()), c.minusOne()));
                    cases.add(new Case(FpAssign(x, c.posInf()), c.posInf()));
                }
                case LOG -> {
                    cases.add(new Case(Lt(x, c.zero()), c.nan()));
                    cases.add(new Case(Eq(x, c.zero()), c.negInf()));
                    cases.add(new Case(FpAssign(x, c.one()), c.zero()));
                    cases.add(new Case(FpAssign(x, c.posInf()), c.posInf()));
                }
                case LOG1P -> {
                    cases.add(new Case(Lt(x, c.minusOne()), c.nan()));
                    cases.add(new Case(FpAssign(x, c.minusOne()), c.negInf()));
                    cases.add(new Case(Eq(x, c.zero()), x));
                    cases.add(new Case(FpAssign(x, c.posInf()), c.posInf()));
                }
                case SIN -> {
                    cases.add(new Case(IsInfinite(x), c.nan()));
                    cases.add(new Case(Eq(x, c.zero()), x));
                }
                case COS -> {
                    cases.add(new Case(IsInfinite(x), c.nan()));
                    cases.add(new Case(Eq(x, c.zero()), c.one()));
                }
                case TANH, ERF -> {
                    cases.add(new Case(Eq(x, c.zero()), x));
                    cases.add(new Case(FpAssign(x, c.posInf()), c.one()));
                    cases.add(new Case(FpAssign(x, c.negInf()), c.minusOne()));
                }
                case ACOS -> {
                    cases.add(new Case(outsideUnit(x, c), c.nan()));
                    cases.add(new Case(FpAssign(x, c.one()), c.zero()));
                }
                case ASIN -> {
                    cases.add(new Case(outsideUnit(x, c), c.nan()));
                    cases.add(new Case(Eq(x, c.zero()), x));
                }
                case ATANH -> {
                    cases.add(new Case(outsideUnit(x, c), c.nan()));
                    cases.add(new Case(FpAssign(x, c.one()), c.posInf()));
                    cases.add(new Case(FpAssign(x, c.minusOne()), c.negInf()));
                    cases.add(new Case(Eq(x, c.zero()), x));
                }
            }
            return cases;
        }

        private static Expr<BoolType> outsideUnit(final Expr<FpType> x, final Consts c) {
            return Or(Lt(x, c.minusOne()), Gt(x, c.one()));
        }

        /** Bounds on the result {@code r} by representable values, beyond the special cases. */
        private List<Expr<BoolType>> bounds(
                final Expr<FpType> x, final Expr<FpType> r, final Consts c) {
            final Expr<BoolType> notNan = Not(IsNan(x));
            final Expr<BoolType> finite = Not(Or(IsNan(x), IsInfinite(x)));
            final Expr<BoolType> unitRange = And(Geq(r, c.minusOne()), Leq(r, c.one()));
            final Expr<BoolType> finiteR = Not(Or(IsNan(r), IsInfinite(r)));
            final Expr<BoolType> inUnit = And(Geq(x, c.minusOne()), Leq(x, c.one()));
            final Expr<BoolType> strictlyInUnit = And(Gt(x, c.minusOne()), Lt(x, c.one()));
            return switch (this) {
                case EXP ->
                        List.of(
                                Imply(notNan, Geq(r, c.zero())),
                                Imply(Gt(x, c.zero()), Geq(r, c.one())),
                                Imply(Lt(x, c.zero()), Leq(r, c.one())));
                case EXPM1 ->
                        List.of(
                                Imply(notNan, Geq(r, c.minusOne())),
                                Imply(Gt(x, c.zero()), Geq(r, c.zero())),
                                Imply(Lt(x, c.zero()), Leq(r, c.zero())));
                case LOG ->
                        List.of(
                                Imply(And(Gt(x, c.zero()), finite), finiteR),
                                Imply(And(Gt(x, c.zero()), Lt(x, c.one())), Leq(r, c.zero())),
                                Imply(Gt(x, c.one()), Geq(r, c.zero())));
                case LOG1P ->
                        List.of(
                                Imply(And(Gt(x, c.minusOne()), finite), finiteR),
                                Imply(Gt(x, c.zero()), Geq(r, c.zero())),
                                Imply(And(Gt(x, c.minusOne()), Lt(x, c.zero())), Leq(r, c.zero())));
                case SIN, COS -> List.of(Imply(finite, unitRange));
                case TANH, ERF ->
                        List.of(
                                Imply(notNan, unitRange),
                                Imply(Gt(x, c.zero()), Geq(r, c.zero())),
                                Imply(Lt(x, c.zero()), Leq(r, c.zero())));
                // acos is within [0, pi] and asin within [-pi/2, pi/2]; 4 and 2 bound them.
                case ACOS -> List.of(Imply(inUnit, And(Geq(r, c.zero()), Leq(r, c.four()))));
                // Outside [-1, 1] the result is NaN, so the sign rules stop at the domain.
                case ASIN ->
                        List.of(
                                Imply(inUnit, And(Geq(r, c.two().neg()), Leq(r, c.two()))),
                                Imply(And(inUnit, Gt(x, c.zero())), Geq(r, c.zero())),
                                Imply(And(inUnit, Lt(x, c.zero())), Leq(r, c.zero())));
                case ATANH ->
                        List.of(
                                Imply(strictlyInUnit, finiteR),
                                Imply(And(inUnit, Gt(x, c.zero())), Geq(r, c.zero())),
                                Imply(And(inUnit, Lt(x, c.zero())), Leq(r, c.zero())));
            };
        }

        /** Everything known about {@code r = f(x)}: the special values and the range bounds. */
        public List<Expr<BoolType>> facts(final Expr<FpType> x, final Expr<FpType> r) {
            final Consts c = Consts.of(x.getType());
            final List<Expr<BoolType>> facts = new ArrayList<>();
            for (final Case special : cases(x, c)) {
                facts.add(Imply(special.guard(), FpAssign(r, special.value())));
            }
            facts.addAll(bounds(x, r, c));
            return facts;
        }

        /** The exact result for a special input, or empty when only the solver can tell. */
        public Optional<FpLitExpr> specialValue(final FpLitExpr x) {
            final var empty = ImmutableValuation.empty();
            for (final Case special : cases(x, Consts.of(x.getType()))) {
                if (((BoolLitExpr) special.guard().eval(empty)).getValue()) {
                    return Optional.of((FpLitExpr) special.value().eval(empty));
                }
            }
            return Optional.empty();
        }
    }

    private static final int HASH_SEED = 6672;

    private final Function function;

    private FpMathFuncExpr(final Function function, final Expr<FpType> op) {
        super(op);
        this.function = checkNotNull(function);
    }

    public static FpMathFuncExpr of(final Function function, final Expr<FpType> op) {
        return new FpMathFuncExpr(function, castFp(op));
    }

    public static FpMathFuncExpr create(final Function function, final Expr<?> op) {
        checkNotNull(op);
        return FpMathFuncExpr.of(function, castFp(op));
    }

    public Function getFunction() {
        return function;
    }

    /** {@link Function#facts} for this application. */
    public List<Expr<BoolType>> facts() {
        return function.facts(getOp(), this);
    }

    @Override
    public FpType getType() {
        return getOp().getType();
    }

    @Override
    public FpLitExpr eval(final Valuation val) {
        final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);
        return function.specialValue(opVal)
                .orElseThrow(
                        () ->
                                new UnsupportedOperationException(
                                        function.getLabel()
                                                + " has no exact value at "
                                                + opVal
                                                + ": it is left to the solver"));
    }

    @Override
    public FpMathFuncExpr with(final Expr<FpType> op) {
        if (op == getOp()) {
            return this;
        } else {
            return FpMathFuncExpr.of(function, op);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final FpMathFuncExpr that = (FpMathFuncExpr) obj;
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
