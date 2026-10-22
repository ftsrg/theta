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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.mdd.mddtoexpr.MddToExprNodeLevel;
import hu.bme.mit.theta.common.exception.NotSolvableException;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.model.BasicSubstitution;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Keys over symbols for next-state levels: a value that depends on symbols on the path look-ahead
 * found is either a source key it equals, or a symbol named by the transition and the source keys
 * it reads, which the transition defines in the path condition.
 */
public final class SymbolicKeys {

    // the decls that are diagram levels; other indexed decls are steps inside one transition
    private static Set<Decl<?>> levels = Set.of();

    private static final Map<List<Object>, ConstDecl<?>> names = new HashMap<>();
    private static final Map<List<Object>, Boolean> functional = new HashMap<>();

    private SymbolicKeys() {}

    public static void setLevels(Set<Decl<?>> levels) {
        SymbolicKeys.levels = levels;
        names.clear();
        functional.clear();
    }

    static boolean isIntermediate(Decl<?> decl) {
        return decl instanceof IndexedConstDecl<?> && !levels.contains(decl);
    }

    private static boolean isSource(Decl<?> decl) {
        return levels.contains(decl) && ((IndexedConstDecl<?>) decl).getIndex() == 0;
    }

    private static boolean isSymbol(Decl<?> decl) {
        return !(decl instanceof IndexedConstDecl<?>);
    }

    /** An edge: its key, the relation below it (null: substitute the key), and what it covers. */
    record Choice(Expr<?> key, Expr<BoolType> child, Expr<BoolType> covered) {}

    /**
     * The edge for the next-state {@code decl} of {@code expr} in {@code model}, where it is {@code
     * value}, or null if the literal is the edge.
     */
    static Choice choose(
            Expr<BoolType> expr,
            Decl<?> decl,
            LitExpr<?> value,
            Valuation model,
            MddHandle lookAhead,
            SolverPool solverPool) {
        if (decl.getType() instanceof BoolType || decl.getType() instanceof EnumType) return null;
        final Map<Decl<?>, Expr<?>> path = path(lookAhead, model);
        final Map<Decl<?>, Expr<?>> read = new HashMap<>();
        boolean symbolic = false;
        for (ConstDecl<?> c : ExprUtils.getConstants(expr)) {
            if (isSymbol(c)) symbolic = true;
            if (isSource(c) && path.containsKey(c)) {
                read.put(c, path.get(c));
                symbolic |= !(path.get(c) instanceof LitExpr<?>);
            }
        }
        if (!symbolic) return null;

        final BasicSubstitution.Builder sub = BasicSubstitution.builder();
        read.forEach(sub::put);
        final Expr<BoolType> onPath = ExprUtils.simplify(sub.build().apply(expr));
        if (!isSat(And(onPath, Neq(decl.getRef(), value)), solverPool)) return null;

        for (Expr<?> key : read.values()) {
            if (!(key instanceof LitExpr<?>)
                    && key.getType().equals(decl.getType())
                    && value.equals(ExprUtils.simplify(key, model))
                    && !isSat(And(onPath, Neq(decl.getRef(), key)), solverPool)) {
                return new Choice(key, null, Eq(decl.getRef(), key));
            }
        }

        if (!isFunctional(onPath, decl, solverPool)) return null;
        final ConstDecl<?> symbol =
                names.computeIfAbsent(
                        List.of(expr, decl, read),
                        n ->
                                Decls.Const(
                                        "__theta_def_" + names.size() + "_" + decl.getName(),
                                        decl.getType()));
        final List<Expr<BoolType>> sources = new ArrayList<>();
        read.forEach((d, k) -> sources.add(Eq(d.getRef(), k)));
        final Expr<BoolType> child =
                And(
                        ExprUtils.simplify(
                                BasicSubstitution.builder()
                                        .put(decl, symbol.getRef())
                                        .build()
                                        .apply(expr)),
                        And(sources));
        return new Choice(symbol.getRef(), child, And(sources));
    }

    // the source keys of the state the model is in, as far as look-ahead covers it
    private static Map<Decl<?>, Expr<?>> path(MddHandle lookAhead, Valuation model) {
        final Map<Decl<?>, Expr<?>> path = new HashMap<>();
        if (lookAhead == null) return path;
        MddNode node = lookAhead.getNode();
        MddVariable variable = lookAhead.getVariableHandle().getVariable().orElse(null);
        while (node != null && !node.isTerminal() && variable != null) {
            final MddVariable lower = variable.getLower().orElse(null);
            if (!node.isOn(variable)) {
                variable = lower;
                continue;
            }
            if (node.defaultValue() != null) {
                node = node.defaultValue();
                variable = lower;
                continue;
            }
            final Decl<?> d = variable.getTraceInfo(Decl.class);
            MddNode next = null;
            for (var c = node.cursor(); c.moveNext(); ) {
                final Expr<?> key = LitExprConverter.toExpr(c.key(), d.getType());
                if (ExprUtils.simplify(Eq(d.getRef(), key), model) instanceof TrueExpr
                        && taken(c.value(), lower, model)) {
                    path.put(d, key);
                    next = c.value();
                    break;
                }
            }
            node = next;
            variable = lower;
        }
        return path;
    }

    private static boolean taken(MddNode node, MddVariable variable, Valuation model) {
        if (node.isTerminal()) return true;
        final Decl<BoolType> aux =
                MddToExprNodeLevel.INSTANCE.getAuxvarCache().getOrNull(node, variable);
        return aux == null || !(ExprUtils.simplify(aux.getRef(), model) instanceof FalseExpr);
    }

    // one value on the path, so the name of that value means the same in every state
    private static boolean isFunctional(
            Expr<BoolType> onPath, Decl<?> decl, SolverPool solverPool) {
        return functional.computeIfAbsent(
                List.of(onPath, decl),
                k -> {
                    final BasicSubstitution.Builder copy = BasicSubstitution.builder();
                    Decl<?> declCopy = null;
                    for (ConstDecl<?> c : ExprUtils.getConstants(onPath)) {
                        if (isSymbol(c)) continue;
                        final ConstDecl<?> fresh = Decls.Const(c.getName() + "'", c.getType());
                        copy.put(c, fresh.getRef());
                        if (c.equals(decl)) declCopy = fresh;
                    }
                    return declCopy == null
                            || !isSat(
                                    And(
                                            List.of(
                                                    onPath,
                                                    copy.build().apply(onPath),
                                                    Neq(decl.getRef(), declCopy.getRef()))),
                                    solverPool);
                });
    }

    private static boolean isSat(Expr<BoolType> expr, SolverPool solverPool) {
        final var solver = solverPool.requestSolver();
        try (var wpp = new WithPushPop(solver)) {
            solver.add(expr);
            return solver.check().isSat();
        } finally {
            solverPool.returnSolver(solver);
        }
    }

    /**
     * Substitutes the steps inside a transition that the residual defines and drops the rest of
     * what it says about them, which is known to be satisfiable, so only symbols remain; gives up
     * where such steps stay tied to symbols.
     */
    static Expr<BoolType> withoutIntermediates(Expr<BoolType> residual) {
        Expr<BoolType> current = residual;
        for (var d = definition(current); d != null; d = definition(current)) {
            current =
                    ExprUtils.simplify(
                            BasicSubstitution.builder()
                                    .put(d.getKey(), d.getValue())
                                    .build()
                                    .apply(current));
        }
        final List<? extends Expr<BoolType>> conjuncts =
                current instanceof AndExpr and ? and.getOps() : List.of(current);
        final List<Expr<BoolType>> kept = new ArrayList<>();
        for (Expr<BoolType> conjunct : conjuncts) {
            final Set<ConstDecl<?>> constants = ExprUtils.getConstants(conjunct);
            if (constants.stream().noneMatch(SymbolicKeys::isIntermediate)) {
                kept.add(conjunct);
            } else if (constants.stream().anyMatch(SymbolicKeys::isSymbol)) {
                throw new NotSolvableException();
            }
        }
        return And(kept);
    }

    private static Map.Entry<Decl<?>, Expr<?>> definition(Expr<BoolType> expr) {
        final List<? extends Expr<BoolType>> conjuncts =
                expr instanceof AndExpr and ? and.getOps() : List.of(expr);
        for (Expr<BoolType> conjunct : conjuncts) {
            if (conjunct instanceof EqExpr<?> eq) {
                final var left = defines(eq.getLeftOp(), eq.getRightOp());
                if (left != null) return left;
                final var right = defines(eq.getRightOp(), eq.getLeftOp());
                if (right != null) return right;
            }
        }
        return null;
    }

    private static Map.Entry<Decl<?>, Expr<?>> defines(Expr<?> lhs, Expr<?> rhs) {
        if (lhs instanceof RefExpr<?> ref
                && isIntermediate(ref.getDecl())
                && !ExprUtils.getConstants(rhs).contains(ref.getDecl())) {
            return Map.entry(ref.getDecl(), rhs);
        }
        return null;
    }
}
