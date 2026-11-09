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
package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static java.util.Collections.singleton;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.StmtApplier.ApplyResult;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

public final class ExplStmtTransFunc implements TransFunc<ExplState, StmtAction, ExplPrec> {

    private final Solver solver;
    // 0 means arbitrarily many
    private final int maxSuccToEnumerate;

    private ExplStmtTransFunc(final Solver solver, final int maxSuccToEnumerate) {
        this.solver = checkNotNull(solver);
        this.maxSuccToEnumerate = maxSuccToEnumerate;
    }

    public static ExplStmtTransFunc create(final Solver solver, final int maxSuccToEnumerate) {
        checkArgument(maxSuccToEnumerate >= 0, "Max. succ. to enumerate must be non-negative.");
        return new ExplStmtTransFunc(solver, maxSuccToEnumerate);
    }

    @Override
    public Collection<ExplState> getSuccStates(
            final ExplState state, final StmtAction action, final ExplPrec prec) {
        return getSuccStates(state, action.getStmts(), prec);
    }

    Collection<ExplState> getSuccStates(
            final ExplState state, final List<Stmt> stmts, final ExplPrec prec) {
        final MutableValuation val = MutableValuation.copyOf(state);
        boolean triedSolver = false;

        for (int i = 0; i < stmts.size(); i++) {
            final Stmt stmt = stmts.get(i);
            final ApplyResult applyResult = StmtApplier.apply(stmt, val, triedSolver);

            assert !triedSolver || applyResult != ApplyResult.BOTTOM;

            if (applyResult == ApplyResult.BOTTOM) {
                return singleton(ExplState.bottom());
            } else if (applyResult == ApplyResult.FAILURE) {
                triedSolver = true;
                final Collection<ExplState> succStates =
                        enumerate(val, stmts.subList(i, stmts.size()), prec::createState);
                if (succStates.isEmpty()) {
                    return singleton(ExplState.bottom());
                } else if (fitsLimit(succStates)) {
                    return succStates;
                }
                // The rest of the edge has too many successors together, but this statement
                // alone may not (an assume pinning a slot witness next to an unconstrained one):
                // enumerate it alone and continue the edge from each of its successors.
                final Collection<ExplState> stmtSuccs =
                        enumerate(val, List.of(stmt), ExplState::of);
                if (stmtSuccs.isEmpty()) {
                    return singleton(ExplState.bottom());
                } else if (fitsLimit(stmtSuccs)) {
                    final List<Stmt> rest = stmts.subList(i + 1, stmts.size());
                    final List<ExplState> result = new ArrayList<>();
                    for (final ExplState succ : stmtSuccs) {
                        result.addAll(getSuccStates(succ, rest, prec));
                    }
                    return result;
                }
                final ApplyResult reapplyResult = StmtApplier.apply(stmt, val, true);
                assert reapplyResult == ApplyResult.SUCCESS;
                // Only this statement had too many successors: a later one (e.g. a havoc
                // and the assume that pins it) may still be enumerable from the new values.
                triedSolver = false;
            }
        }

        final ExplState abstracted = prec.createState(val);
        return singleton(abstracted);
    }

    private boolean fitsLimit(final Collection<ExplState> succStates) {
        return maxSuccToEnumerate == 0 || succStates.size() <= maxSuccToEnumerate;
    }

    /**
     * The successors of [stmts] from [val] by the solver, at most one more than the limit (to tell
     * whether there are more). The solver only gets the values of the variables the statements
     * mention: the others are independent of them and keep their values, which are added back to
     * each successor. A large valuation (memory arrays, say) would otherwise go into every query.
     */
    private Collection<ExplState> enumerate(
            final Valuation val,
            final List<Stmt> stmts,
            final Function<Valuation, ExplState> createState) {
        final StmtUnfoldResult toExprResult =
                StmtUtils.toExpr(stmts, VarIndexingFactory.indexing(0));
        final Set<VarDecl<?>> mentioned = StmtUtils.getVars(stmts);
        final MutableValuation relevant = new MutableValuation();
        final MutableValuation untouched = new MutableValuation();
        for (final Decl<?> decl : val.getDecls()) {
            (mentioned.contains(decl) ? relevant : untouched)
                    .put(decl, val.eval(decl).orElseThrow());
        }
        final Expr<BoolType> expr = And(relevant.toExpr(), And(toExprResult.getExprs()));
        final VarIndexing nextIdx = toExprResult.getIndexing();
        final int maxToQuery = maxSuccToEnumerate == 0 ? 0 : maxSuccToEnumerate + 1;
        return ExprStates.createStatesForExpr(
                        solver, expr, 0, createState::apply, nextIdx, maxToQuery)
                .stream()
                .map(succ -> withValues(succ, untouched, createState))
                .toList();
    }

    private static ExplState withValues(
            final ExplState state,
            final Valuation values,
            final Function<Valuation, ExplState> createState) {
        if (state.isBottom() || values.getDecls().isEmpty()) {
            return state;
        }
        final MutableValuation merged = MutableValuation.copyOf(values);
        state.getDecls().forEach(decl -> merged.put(decl, state.eval(decl).orElseThrow()));
        return createState.apply(merged);
    }
}
