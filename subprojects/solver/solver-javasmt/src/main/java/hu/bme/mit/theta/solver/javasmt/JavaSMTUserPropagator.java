/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

public abstract class JavaSMTUserPropagator extends AbstractUserPropagator {
    private Function<Expr<?>, Formula> toTerm;
    private Function<Formula, Expr<?>> toExpr;
    private final Map<Expr<BoolType>, BooleanFormula> registeredTerms;

    protected JavaSMTUserPropagator() {
        super();
        registeredTerms = new LinkedHashMap<>();
    }

    final void setToTerm(final Function<Expr<?>, Formula> toTerm) {
        this.toTerm = toTerm;
    }

    final void setToExpr(final Function<Formula, Expr<?>> toExpr) {
        this.toExpr = toExpr;
    }

    @Override
    protected final PropagatorBackend getBackend() {
        return super.getBackend();
    }

    /**
     * Gets called when the solver decides on the value for a bool expression. Can call propagate*
     * calls from here. When overriding, no need to call super.
     *
     * @param expr The expression for which a value became available
     * @param value The value of the expression
     */
    public void onKnownValue(final Expr<BoolType> expr, final boolean value) {}

    @Override
    public final void onKnownValue(final BooleanFormula expr, final boolean value) {
        super.onKnownValue(expr, value);
        final var entry =
                registeredTerms.entrySet().stream()
                        .filter(e -> e.getValue().equals(expr))
                        .findAny();
        final var tExpr =
                entry.isPresent() ? entry.get().getKey() : cast(toExpr.apply(expr), Bool());
        onKnownValue(tExpr, value);
    }

    /**
     * Gets called when a branching is done on a registered expression. Change the decision by
     * calling propagateNextDecision.
     *
     * @param expr
     * @param value
     */
    public void onDecision(final Expr<BoolType> expr, final boolean value) {}

    @Override
    public final void onDecision(final BooleanFormula expr, final boolean value) {
        super.onDecision(expr, value);
        final var tExpr = cast(toExpr.apply(expr), Bool());
        onDecision(tExpr, value);
    }

    @Override
    public final void initializeWithBackend(final PropagatorBackend pBackend) {
        super.initializeWithBackend(pBackend);
        getBackend().notifyOnFinalCheck();
        getBackend().notifyOnKnownValue();
        getBackend().notifyOnDecision();
    }

    /**
     * Register an expression with the propagator. Does NOT add it to the solver.
     *
     * @param expr The expression to register
     */
    public void registerExpression(final Expr<BoolType> expr) {
        final BooleanFormula booleanFormula = (BooleanFormula) toTerm.apply(expr);
        registeredTerms.put(expr, booleanFormula);
        registerExpression(booleanFormula);
    }

    @Override
    public final void registerExpression(final BooleanFormula theoryExpr) {
        super.registerExpression(theoryExpr);
    }

    public final void propagateConflict(final List<Expr<BoolType>> exprs) {
        final var terms = exprs.stream().map(registeredTerms::get).toArray(BooleanFormula[]::new);
        checkState(Arrays.stream(terms).noneMatch(Objects::isNull));
        getBackend().propagateConflict(terms);
    }

    public final void propagateConsequence(
            final List<Expr<BoolType>> exprs, final Expr<BoolType> consequence) {
        final var terms = exprs.stream().map(registeredTerms::get).toArray(BooleanFormula[]::new);
        for (var expr : exprs) {
            if (registeredTerms.get(expr) == null) {
                System.err.println(expr);
            }
        }
        checkState(
                Arrays.stream(terms).noneMatch(Objects::isNull),
                "Registered terms failed to look up one or more expressions from %s. Registered"
                        + " terms: %s",
                exprs,
                registeredTerms.keySet());
        final BooleanFormula consequenceTerm = (BooleanFormula) toTerm.apply(consequence);
        getBackend().propagateConsequence(terms, consequenceTerm);
    }

    public final boolean propagateNextDecision(
            final Expr<BoolType> formula, Optional<Boolean> optional) {
        final BooleanFormula term = (BooleanFormula) toTerm.apply(formula);
        return getBackend().propagateNextDecision(term, optional);
    }
}
