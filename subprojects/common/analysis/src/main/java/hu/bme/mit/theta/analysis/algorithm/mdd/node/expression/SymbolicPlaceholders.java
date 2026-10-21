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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddUnsafeTemplateBuilder;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate;
import hu.bme.mit.theta.common.exception.NotSolvableException;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.model.BasicSubstitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.utils.ExprUtils;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A next-state value defined by a lower level is not known where its key is chosen, so the edge
 * gets a placeholder; the relational product then splits the states below by the term the
 * placeholder is bound to in their path conditions, and uses those terms as keys.
 */
public final class SymbolicPlaceholders {

    private static final Map<Decl<?>, ConstDecl<?>> placeholders = new HashMap<>();
    // each placeholder with the variable whose next-state value it stands for
    private static final Map<ConstDecl<?>, Decl<?>> known = new HashMap<>();

    // the decls that are diagram levels; other indexed decls are steps inside one transition
    private static Set<Decl<?>> levels = Set.of();

    private SymbolicPlaceholders() {}

    public static void setLevels(Set<Decl<?>> levels) {
        SymbolicPlaceholders.levels = levels;
    }

    static boolean isIntermediate(Decl<?> decl) {
        return decl instanceof IndexedConstDecl<?> && !levels.contains(decl);
    }

    static boolean isLevel(Decl<?> decl) {
        return levels.contains(decl);
    }

    // the variables whose next value can depend on a symbol; only they need placeholders
    private static Set<Decl<?>> tainted = Set.of();

    static boolean isTainted(Decl<?> decl) {
        return tainted.contains(variableOf(decl));
    }

    /**
     * Collects the variables a symbol can reach: a conjunct that mentions a symbol or a reached
     * variable reaches every next-state variable in it.
     */
    public static void setTainted(List<Expr<BoolType>> transitions) {
        final Set<Decl<?>> reached = new HashSet<>();
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Expr<BoolType> transition : transitions) {
                final List<? extends Expr<BoolType>> conjuncts =
                        transition instanceof AndExpr and ? and.getOps() : List.of(transition);
                for (Expr<BoolType> conjunct : conjuncts) {
                    final Set<ConstDecl<?>> constants = ExprUtils.getConstants(conjunct);
                    if (constants.stream()
                            .noneMatch(
                                    c ->
                                            !(c instanceof IndexedConstDecl<?>)
                                                    || reached.contains(variableOf(c)))) {
                        continue;
                    }
                    for (ConstDecl<?> c : constants) {
                        if (c instanceof IndexedConstDecl<?> indexed && indexed.getIndex() > 0) {
                            changed |= reached.add(indexed.getVarDecl());
                        }
                    }
                }
            }
        }
        tainted = reached;
    }

    public static Set<Decl<?>> getTainted() {
        return tainted;
    }

    /**
     * Substitutes the steps inside a transition that an equality defines, for the variables a
     * symbol can reach; the others stay named, which keeps long chains of steps small.
     */
    public static Expr<BoolType> eliminateIntermediates(Expr<BoolType> expr) {
        if (tainted.isEmpty()) return expr;
        Expr<BoolType> current = ExprUtils.simplify(expr);
        while (true) {
            final Map.Entry<Decl<?>, Expr<?>> definition = definition(current);
            if (definition == null) return current;
            current =
                    ExprUtils.simplify(
                            BasicSubstitution.builder()
                                    .put(definition.getKey(), definition.getValue())
                                    .build()
                                    .apply(current));
        }
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
                && isTainted(ref.getDecl())
                && !ExprUtils.getConstants(rhs).contains(ref.getDecl())) {
            return Map.entry(ref.getDecl(), rhs);
        }
        return null;
    }

    /**
     * Drops what a residual says about steps inside a transition, which is already known to be
     * satisfiable, so only symbols remain; gives up where such steps are tied to symbols.
     */
    static Expr<BoolType> withoutIntermediates(Expr<BoolType> residual) {
        final List<? extends Expr<BoolType>> conjuncts =
                residual instanceof AndExpr and ? and.getOps() : List.of(residual);
        final List<Expr<BoolType>> kept = new ArrayList<>();
        for (Expr<BoolType> conjunct : conjuncts) {
            final Set<ConstDecl<?>> constants = ExprUtils.getConstants(conjunct);
            if (constants.stream().noneMatch(SymbolicPlaceholders::isIntermediate)) {
                kept.add(conjunct);
            } else if (constants.stream().anyMatch(c -> !(c instanceof IndexedConstDecl<?>))) {
                throw new NotSolvableException();
            }
        }
        return SmartBoolExprs.And(kept);
    }

    static ConstDecl<?> of(Decl<?> decl) {
        return placeholders.computeIfAbsent(
                decl,
                d -> {
                    final ConstDecl<?> placeholder =
                            Decls.Const("__theta_next_" + d.getName(), d.getType());
                    known.put(placeholder, variableOf(d));
                    return placeholder;
                });
    }

    private static Decl<?> variableOf(Decl<?> decl) {
        return decl instanceof IndexedConstDecl<?> indexed ? indexed.getVarDecl() : decl;
    }

    // only the placeholder of this level's own variable is resolved here; an outer one that a
    // key equals or mentions is resolved, keys included, where it was introduced
    private static ConstDecl<?> placeholderOf(int key, MddVariable variable) {
        if (!LitExprConverter.isSymbolic()) return null;
        final Decl<?> decl = variable.getTraceInfo(Decl.class);
        if (decl == null) return null;
        final Expr<?> value = LitExprConverter.toExpr(key, decl.getType());
        if (value instanceof RefExpr<?> ref
                && ref.getDecl() instanceof ConstDecl<?> c
                && variableOf(decl).equals(known.get(c))) {
            return c;
        }
        return null;
    }

    /**
     * The states below the edge {@code key} of {@code variable}, keyed by the bound term, or null
     * if the key is not a placeholder.
     */
    public static Map<Integer, MddNode> lift(int key, MddNode below, MddVariable variable) {
        final ConstDecl<?> placeholder = placeholderOf(key, variable);
        if (placeholder == null) return null;
        return new Lifter(placeholder, variable.getMddGraph())
                .lift(below, variable.getLower().orElse(null));
    }

    private static final class Lifter {
        private final ConstDecl<?> placeholder;
        private final MddGraph<Expr> graph;
        private final Map<MddNode, Map<Integer, MddNode>> memo = new HashMap<>();

        @SuppressWarnings("unchecked")
        private Lifter(ConstDecl<?> placeholder, MddGraph<?> graph) {
            this.placeholder = placeholder;
            this.graph = (MddGraph<Expr>) graph;
        }

        Map<Integer, MddNode> lift(MddNode node, MddVariable variable) {
            if (node == null || node == graph.getTerminalZeroNode()) return Map.of();
            final Map<Integer, MddNode> cached = memo.get(node);
            if (cached != null) return cached;
            final Map<Integer, MddNode> result;
            if (node.isTerminal()) {
                result = liftTerminal(node);
            } else if (!node.isOn(variable)) {
                result = lift(node, variable.getLower().orElse(null));
            } else {
                final MddVariable lower = variable.getLower().orElse(null);
                if (node.defaultValue() != null) {
                    result = new LinkedHashMap<>();
                    lift(node.defaultValue(), lower)
                            .forEach(
                                    (k, child) ->
                                            result.put(
                                                    k,
                                                    variable.checkInNode(
                                                            MddStructuralTemplate.of(
                                                                    IntObjMapView.empty(child)))));
                } else {
                    final var type = variable.getTraceInfo(Decl.class).getType();
                    final Map<Integer, MddUnsafeTemplateBuilder> builders = new LinkedHashMap<>();
                    for (var c = node.cursor(); c.moveNext(); ) {
                        final int key = c.key();
                        final Expr<?> keyValue = LitExprConverter.toExpr(key, type);
                        lift(c.value(), lower)
                                .forEach(
                                        (k, child) -> {
                                            if (child == graph.getTerminalZeroNode()) return;
                                            // a key computed from the placeholder gets its value
                                            final int edge =
                                                    mentions(keyValue)
                                                            ? LitExprConverter.toInt(
                                                                    substitute(keyValue, k))
                                                            : key;
                                            final var builder =
                                                    builders.computeIfAbsent(
                                                            k,
                                                            x ->
                                                                    JavaMddFactory.getDefault()
                                                                            .createUnsafeTemplateBuilder());
                                            final MddNode existing = builder.get(edge);
                                            builder.set(
                                                    edge,
                                                    existing == null
                                                            ? child
                                                            : lower == null
                                                                    ? graph.unionTerminal(
                                                                            existing, child)
                                                                    : lower.union(existing, child));
                                        });
                    }
                    result = new LinkedHashMap<>();
                    builders.forEach(
                            (k, builder) ->
                                    result.put(
                                            k,
                                            variable.checkInNode(
                                                    MddStructuralTemplate.of(
                                                            builder.buildAndReset()))));
                }
            }
            memo.put(node, result);
            return result;
        }

        @SuppressWarnings("unchecked")
        private Map<Integer, MddNode> liftTerminal(MddNode terminal) {
            final Expr<BoolType> condition =
                    (Expr<BoolType>) ((MddNode.Terminal<?>) terminal).getTerminalData();
            final Map<Integer, MddNode> result = new LinkedHashMap<>();
            for (Expr<BoolType> disjunct : disjuncts(condition)) {
                final Expr<?> bound = binding(disjunct);
                if (bound == null) throw new NotSolvableException();
                final Expr<BoolType> rest =
                        ExprUtils.simplify(
                                BasicSubstitution.builder()
                                        .put(placeholder, bound)
                                        .build()
                                        .apply(disjunct));
                // a single disjunct of a satisfiable condition may still be unsatisfiable
                final MddNode restNode =
                        graph.intersectionTerminal(
                                graph.getNodeFor(rest), graph.getNodeFor(True()));
                if (restNode == graph.getTerminalZeroNode()) continue;
                result.merge(LitExprConverter.toInt(bound), restNode, graph::unionTerminal);
            }
            return result;
        }

        private List<Expr<BoolType>> disjuncts(Expr<BoolType> expr) {
            if (expr instanceof OrExpr or) {
                return or.getOps().stream().flatMap(op -> disjuncts(op).stream()).toList();
            }
            return expr.equals(False()) ? List.of() : List.of(expr);
        }

        private Expr<?> substitute(Expr<?> expr, int boundKey) {
            final Expr<?> bound = LitExprConverter.toExpr(boundKey, placeholder.getType());
            return ExprUtils.simplify(
                    BasicSubstitution.builder().put(placeholder, bound).build().apply(expr));
        }

        // a term free of placeholders is preferred, since an outer one is only resolved later
        private Expr<?> binding(Expr<BoolType> disjunct) {
            final List<? extends Expr<BoolType>> conjuncts =
                    disjunct instanceof AndExpr and ? and.getOps() : List.of(disjunct);
            Expr<?> open = null;
            for (Expr<BoolType> conjunct : conjuncts) {
                if (conjunct instanceof EqExpr<?> eq) {
                    final Expr<?> bound =
                            isPlaceholder(eq.getLeftOp()) && !mentions(eq.getRightOp())
                                    ? eq.getRightOp()
                                    : isPlaceholder(eq.getRightOp()) && !mentions(eq.getLeftOp())
                                            ? eq.getLeftOp()
                                            : null;
                    if (bound == null) continue;
                    if (ExprUtils.getConstants(bound).stream().noneMatch(known::containsKey)) {
                        return bound;
                    }
                    if (open == null) open = bound;
                }
            }
            return open;
        }

        private boolean isPlaceholder(Expr<?> expr) {
            return expr instanceof RefExpr<?> ref && ref.getDecl().equals(placeholder);
        }

        private boolean mentions(Expr<?> expr) {
            return ExprUtils.getConstants(expr).contains(placeholder);
        }
    }
}
