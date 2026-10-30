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
package hu.bme.mit.theta.solver.javasmt;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.UserPropagator;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Function;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.PropagatorBackend;
import org.sosy_lab.java_smt.basicimpl.AbstractUserPropagator;

/** Binds a {@link UserPropagator} to a JavaSMT prover, translating between exprs and formulas. */
final class JavaSMTUserPropagator extends AbstractUserPropagator implements UserPropagator.Backend {
    private final UserPropagator propagator;
    private final Function<Expr<?>, Formula> toTerm;
    private final Function<Formula, Expr<?>> toExpr;
    private final Map<Expr<BoolType>, BooleanFormula> registeredTerms;
    private final Map<BooleanFormula, Expr<BoolType>> registeredExprs;

    JavaSMTUserPropagator(
            final UserPropagator propagator,
            final Function<Expr<?>, Formula> toTerm,
            final Function<Formula, Expr<?>> toExpr) {
        this.propagator = propagator;
        this.toTerm = toTerm;
        this.toExpr = toExpr;
        registeredTerms = new LinkedHashMap<>();
        registeredExprs = new LinkedHashMap<>();
    }

    private Expr<BoolType> toBoolExpr(final BooleanFormula formula) {
        final Expr<BoolType> registered = registeredExprs.get(formula);
        return registered != null ? registered : cast(toExpr.apply(formula), Bool());
    }

    @Override
    public void initializeWithBackend(final PropagatorBackend pBackend) {
        super.initializeWithBackend(pBackend);
        getBackend().notifyOnFinalCheck();
        getBackend().notifyOnKnownValue();
        getBackend().notifyOnDecision();
    }

    @Override
    public void onKnownValue(final BooleanFormula expr, final boolean value) {
        propagator.onKnownValue(toBoolExpr(expr), value);
    }

    @Override
    public void onDecision(final BooleanFormula expr, final boolean value) {
        propagator.onDecision(toBoolExpr(expr), value);
    }

    @Override
    public void onFinalCheck() {
        propagator.onFinalCheck();
    }

    @Override
    public void onPush() {
        propagator.onPush();
    }

    @Override
    public void onPop(final int levels) {
        propagator.onPop(levels);
    }

    @Override
    public void registerExpression(final Expr<BoolType> expr) {
        final BooleanFormula term = (BooleanFormula) toTerm.apply(expr);
        registeredTerms.put(expr, term);
        registeredExprs.putIfAbsent(term, expr);
        registerExpression(term);
    }

    private BooleanFormula[] registered(final List<Expr<BoolType>> exprs) {
        final var terms = exprs.stream().map(registeredTerms::get).toArray(BooleanFormula[]::new);
        checkState(
                Arrays.stream(terms).noneMatch(Objects::isNull),
                "Registered terms failed to look up one or more expressions from %s. Registered"
                        + " terms: %s",
                exprs,
                registeredTerms.keySet());
        return terms;
    }

    @Override
    public void propagateConflict(final List<Expr<BoolType>> exprs) {
        getBackend().propagateConflict(registered(exprs));
    }

    @Override
    public void propagateConsequence(
            final List<Expr<BoolType>> exprs, final Expr<BoolType> consequence) {
        getBackend()
                .propagateConsequence(
                        registered(exprs), (BooleanFormula) toTerm.apply(consequence));
    }

    @Override
    public boolean propagateNextDecision(final Expr<BoolType> expr, final Optional<Boolean> value) {
        return getBackend().propagateNextDecision((BooleanFormula) toTerm.apply(expr), value);
    }

    @Override
    public String toString() {
        return propagator.toString();
    }
}
