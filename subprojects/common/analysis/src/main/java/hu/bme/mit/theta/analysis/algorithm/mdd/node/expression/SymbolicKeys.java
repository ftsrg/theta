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

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.java.mdd.UnaryOperationCache;
import hu.bme.mit.theta.analysis.algorithm.mdd.mddtoexpr.MddToExprNodeLevel;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.BasicSubstitution;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.QuantifiedExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * Symbolic values: a key is a literal or the token, which leaves the value of its variable to the
 * terminal below, a formula over the current values of the token variables. A step conjoins what
 * the relation leaves over and projects the overwritten values out; what cannot be eliminated is
 * kept under a name bound in that formula.
 */
public final class SymbolicKeys {

    // the decls that are diagram levels; other indexed decls are steps inside one transition
    private static Set<Decl<?>> levels = Set.of();

    // a conjunct of a relation below a written next-state level, so its terminal knows the write
    private static final Map<Decl<?>, ConstDecl<BoolType>> markers = new HashMap<>();
    private static final Map<ConstDecl<BoolType>, Decl<?>> written = new HashMap<>();

    private static final Map<List<Object>, ConstDecl<?>> boundNames = new HashMap<>();
    private static final String BOUND = "__theta_old_";

    private SymbolicKeys() {}

    // the solvers that eliminate what the substitutions leave over
    private static SolverPool qeSolvers;
    private static final Map<List<Object>, ParamDecl<?>> qeParams = new HashMap<>();

    public static void setLevels(Set<Decl<?>> levels, SolverPool solverPool) {
        SymbolicKeys.levels = levels;
        qeSolvers = solverPool;
        markers.clear();
        written.clear();
        images.clear();
    }

    static boolean isIntermediate(Decl<?> decl) {
        return decl instanceof IndexedConstDecl<?> && !levels.contains(decl);
    }

    static boolean isTarget(Decl<?> decl) {
        return levels.contains(decl) && ((IndexedConstDecl<?>) decl).getIndex() > 0;
    }

    /** Bool and enum values stay literals: their levels are small and fully enumerable. */
    public static boolean canBeToken(Type type) {
        return !(type instanceof BoolType) && !(type instanceof EnumType);
    }

    static Expr<BoolType> marker(Decl<?> target) {
        return markers.computeIfAbsent(
                        target,
                        d -> {
                            final ConstDecl<BoolType> m =
                                    Decls.Const("__theta_w_" + d.getName(), BoolType.getInstance());
                            written.put(m, d);
                            return m;
                        })
                .getRef();
    }

    /** Whether the next-state {@code decl}, {@code value} in {@code model}, takes the token. */
    static boolean takesToken(
            Expr<BoolType> expr,
            Decl<?> decl,
            LitExpr<?> value,
            Valuation model,
            MddHandle lookAhead,
            SolverPool solverPool) {
        if (!canBeToken(decl.getType())) return false;
        final Map<Decl<?>, Expr<?>> keys = new HashMap<>();
        final Expr<BoolType> leaf = path(lookAhead, model, keys);
        final BasicSubstitution.Builder sub = BasicSubstitution.builder();
        keys.forEach(sub::put);
        final Expr<BoolType> onPath = ExprUtils.simplify(sub.build().apply(expr));
        return !hasFewValues(And(onPath, leaf), decl, solverPool);
    }

    // values with at most this many possibilities on a path stay literals
    private static final int FEW = 4;

    /** Whether {@code expr} leaves {@code decl} only a few values, which are then enumerated. */
    static boolean hasFewValues(Expr<BoolType> expr, Decl<?> decl, SolverPool solverPool) {
        final var solver = solverPool.requestSolver();
        try (var wpp = new WithPushPop(solver)) {
            solver.add(expr);
            for (int i = 0; i <= FEW; i++) {
                if (!solver.check().isSat()) return true;
                final var value = solver.getModel().eval(decl);
                if (value.isEmpty()) return false;
                solver.add(Neq(decl.getRef(), value.get()));
            }
            return false;
        } finally {
            solverPool.returnSolver(solver);
        }
    }

    // the literal keys of the state the model is in, as far as look-ahead covers it, and its
    // terminal
    private static Expr<BoolType> path(
            MddHandle lookAhead, Valuation model, Map<Decl<?>, Expr<?>> keys) {
        if (lookAhead == null) return True();
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
            final Expr<?> value = model.eval(d).orElse(null);
            MddNode next = null;
            for (var c = node.cursor(); c.moveNext(); ) {
                final boolean token = LitExprConverter.isToken(c.key());
                final Expr<?> key = LitExprConverter.toExpr(c.key(), d);
                if ((token || key.equals(value)) && taken(c.value(), lower, model)) {
                    if (!token) keys.put(d, key);
                    next = c.value();
                    break;
                }
            }
            node = next;
            variable = lower;
        }
        return node != null && node.isTerminal() ? leafOf(node) : True();
    }

    @SuppressWarnings("unchecked")
    public static Expr<BoolType> leafOf(MddNode terminal) {
        return ((MddNode.Terminal<?>) terminal).getTerminalData() instanceof Expr<?> e
                ? (Expr<BoolType>) e
                : True();
    }

    private static boolean taken(MddNode node, MddVariable variable, Valuation model) {
        if (node.isTerminal())
            return !(ExprUtils.simplify(leafOf(node), model) instanceof FalseExpr);
        final Decl<BoolType> aux =
                MddToExprNodeLevel.INSTANCE.getAuxvarCache().getOrNull(node, variable);
        return aux == null || !(model.eval(aux).orElse(null) instanceof FalseExpr);
    }

    /** What a relation leaves at its terminal, without its own steps where they are defined. */
    static Expr<BoolType> withoutIntermediates(Expr<BoolType> residual) {
        final Set<Decl<?>> eliminated = new HashSet<>();
        for (ConstDecl<?> c : ExprUtils.getConstants(residual))
            if (isIntermediate(c)) eliminated.add(c);
        return eliminate(residual, eliminated);
    }

    /**
     * The terminal after a step: {@code joined} is the source terminal and what the relation left,
     * satisfiable; the values the step overwrote are projected out and the next-state values become
     * current.
     */
    public static Expr<BoolType> image(Expr<BoolType> joined) {
        Expr<BoolType> ret = images.getOrNull(joined);
        if (ret == null) {
            ret = computeImage(joined);
            images.addToCache(joined, ret);
        }
        return ret;
    }

    private static final UnaryOperationCache<Expr<BoolType>, Expr<BoolType>> images =
            new UnaryOperationCache<>();

    // what elimination left over of the eliminated decls is kept under bound names
    private static Expr<BoolType> bindLeftovers(
            Expr<BoolType> expr, Set<Decl<?>> eliminated, BasicSubstitution.Builder bind) {
        final Set<ConstDecl<?>> used = ExprUtils.getConstants(expr);
        int next = 0;
        for (ConstDecl<?> c : used) {
            if (!eliminated.contains(c)) continue;
            ConstDecl<?> name;
            do {
                name = boundName(next++, c.getType());
            } while (used.contains(name));
            bind.put(c, name.getRef());
        }
        return bind.build().apply(expr);
    }

    private static Expr<BoolType> canonical(Expr<BoolType> expr) {
        final Expr<BoolType> result = ExprUtils.canonize(expr);
        return ExprUtils.getConstants(result).isEmpty() ? True() : result;
    }

    private static Expr<BoolType> computeImage(Expr<BoolType> joined) {
        final Set<ConstDecl<?>> constants = ExprUtils.getConstants(joined);
        final Set<Decl<?>> targets = new HashSet<>();
        final BasicSubstitution.Builder unmark = BasicSubstitution.builder();
        for (ConstDecl<?> c : constants) {
            final Decl<?> target = written.get(c);
            if (target != null) {
                targets.add(target);
                unmark.put(c, True());
            }
        }
        Expr<BoolType> current =
                ExprUtils.simplify(
                        normalizeArrays(unmark.build().apply(joined), new UnaryOperationCache<>()));
        final Set<Decl<?>> eliminated = new HashSet<>();
        for (ConstDecl<?> c : ExprUtils.getConstants(current)) {
            if (isIntermediate(c)) eliminated.add(c);
            else if (c instanceof IndexedConstDecl<?> ic && ic.getIndex() == 0) {
                final Decl<?> target = targetOf(ic);
                if (target != null && targets.contains(target)) eliminated.add(c);
            }
        }
        current = eliminate(current, eliminated);
        final BasicSubstitution.Builder bind = BasicSubstitution.builder();
        for (Decl<?> target : targets) {
            bind.put(target, ((IndexedConstDecl<?>) target).getVarDecl().getConstDecl(0).getRef());
        }
        return canonical(bindLeftovers(current, eliminated, bind));
    }

    // reads and writes at literal indices resolved through write chains, writes kept in index order
    @SuppressWarnings({"unchecked", "rawtypes"})
    private static <T extends Type> Expr<T> normalizeArrays(
            Expr<T> expr, UnaryOperationCache<Expr<?>, Expr<?>> memo) {
        final Expr<?> cached = memo.getOrNull(expr);
        if (cached != null) return (Expr<T>) cached;
        Expr<?> result = expr;
        final List<? extends Expr<?>> ops = expr.getOps();
        if (!ops.isEmpty()) {
            final List<Expr<?>> normalized = new ArrayList<>(ops.size());
            boolean changed = false;
            for (Expr<?> op : ops) {
                final Expr<?> n = normalizeArrays(op, memo);
                changed |= n != op;
                normalized.add(n);
            }
            if (changed) result = expr.withOps(normalized);
        }
        if (result instanceof ArrayReadExpr read && read.getIndex() instanceof LitExpr<?> index) {
            Expr<?> array = read.getArray();
            Expr<?> found = null;
            while (found == null
                    && array instanceof ArrayWriteExpr<?, ?> write
                    && write.getIndex() instanceof LitExpr<?> i) {
                if (i.equals(index)) found = write.getElem();
                else array = write.getArray();
            }
            if (found != null) result = found;
            else if (array != read.getArray()) result = read.with((Expr) array, index);
        } else if (result instanceof ArrayWriteExpr write
                && write.getIndex() instanceof LitExpr<?>) {
            final List<ArrayWriteExpr<?, ?>> chain = new ArrayList<>();
            Expr<?> base = result;
            while (base instanceof ArrayWriteExpr<?, ?> w && w.getIndex() instanceof LitExpr<?>) {
                chain.add(w);
                base = w.getArray();
            }
            final Map<Expr<?>, Expr<?>> cells =
                    new TreeMap<>(Comparator.comparing(Object::toString));
            for (ArrayWriteExpr<?, ?> w : chain) cells.putIfAbsent(w.getIndex(), w.getElem());
            Expr rebuilt = base;
            for (var cell : cells.entrySet())
                rebuilt = ArrayWriteExpr.of(rebuilt, (Expr) cell.getKey(), (Expr) cell.getValue());
            if (!rebuilt.equals(result)) result = rebuilt;
        }
        memo.addToCache(expr, result);
        return (Expr<T>) result;
    }

    private static Decl<?> targetOf(IndexedConstDecl<?> source) {
        for (Decl<?> d : levels) {
            if (d instanceof IndexedConstDecl<?> ic
                    && ic.getIndex() > 0
                    && ic.getVarDecl().equals(source.getVarDecl())) return d;
        }
        return null;
    }

    private static ConstDecl<?> boundName(int index, Type type) {
        return boundNames.computeIfAbsent(
                List.of(index, type), k -> Decls.Const(BOUND + index, type));
    }

    static boolean isBound(Decl<?> decl) {
        return decl instanceof ConstDecl<?> && decl.getName().startsWith(BOUND);
    }

    /** {@code b} with its bound names renamed apart from those of {@code a}. */
    static Expr<BoolType> renamedApart(Expr<BoolType> a, Expr<BoolType> b) {
        final Set<ConstDecl<?>> inA = ExprUtils.getConstants(a);
        final Set<ConstDecl<?>> inB = ExprUtils.getConstants(b);
        final BasicSubstitution.Builder rename = BasicSubstitution.builder();
        boolean clash = false;
        int next = 0;
        for (ConstDecl<?> c : inB) {
            if (!isBound(c) || !inA.contains(c)) continue;
            clash = true;
            ConstDecl<?> name;
            do {
                name = boundName(next++, c.getType());
            } while (inA.contains(name) || inB.contains(name));
            rename.put(c, name.getRef());
        }
        return clash ? rename.build().apply(b) : b;
    }

    // and what that leaves over by the solver's quantifier elimination, where it succeeds
    private static Expr<BoolType> eliminate(Expr<BoolType> expr, Set<Decl<?>> eliminated) {
        if (eliminated.isEmpty()) return expr;
        return eliminateQuantifiers(eliminateCheaply(expr, eliminated), eliminated);
    }

    /**
     * Existentially eliminates {@code eliminated} from the satisfiable {@code expr} where that is
     * cheap: by substituting their definitions and dropping the parts that only talk about them and
     * bound names. Leftovers stay in the result.
     */
    private static Expr<BoolType> eliminateCheaply(Expr<BoolType> expr, Set<Decl<?>> eliminated) {
        if (eliminated.isEmpty()) return expr;
        // a definition conjunct is dropped and substituted into the others, then all is simplified
        final List<Expr<BoolType>> remaining =
                new ArrayList<>(expr instanceof AndExpr and ? and.getOps() : List.of(expr));
        final UnaryOperationCache<Expr<?>, Expr<?>> memo = new UnaryOperationCache<>();
        boolean substituted = false;
        for (var d = definition(remaining, eliminated);
                d != null;
                d = definition(remaining, eliminated)) {
            remaining.remove(d.conjunct());
            final var sub = BasicSubstitution.builder().put(d.decl(), d.value()).build();
            remaining.replaceAll(e -> normalizeArrays(sub.apply(e), memo));
            substituted = true;
        }
        final Expr<BoolType> current =
                substituted ? ExprUtils.simplify(And(remaining)) : And(remaining);
        final List<? extends Expr<BoolType>> conjuncts =
                current instanceof AndExpr and ? and.getOps() : List.of(current);
        // conjuncts linked by shared eliminated or bound constants form one closed part, unless
        // one of them mentions anything else
        final int n = conjuncts.size();
        final int[] parent = new int[n];
        for (int i = 0; i < n; i++) parent[i] = i;
        final Map<Decl<?>, Integer> owner = new HashMap<>();
        final boolean[] open = new boolean[n];
        for (int i = 0; i < n; i++) {
            for (ConstDecl<?> c : ExprUtils.getConstants(conjuncts.get(i))) {
                if (eliminated.contains(c) || isBound(c)) {
                    final Integer j = owner.putIfAbsent(c, i);
                    if (j != null) parent[find(parent, i)] = find(parent, j);
                } else {
                    open[i] = true;
                }
            }
        }
        final boolean[] openRoot = new boolean[n];
        for (int i = 0; i < n; i++) if (open[i]) openRoot[find(parent, i)] = true;
        final List<Expr<BoolType>> kept = new ArrayList<>();
        for (int i = 0; i < n; i++) if (openRoot[find(parent, i)]) kept.add(conjuncts.get(i));
        return And(kept);
    }

    private static Expr<BoolType> eliminateQuantifiers(
            Expr<BoolType> expr, Set<Decl<?>> eliminated) {
        final BasicSubstitution.Builder toParams = BasicSubstitution.builder();
        final List<ParamDecl<?>> params = new ArrayList<>();
        for (ConstDecl<?> c : ExprUtils.getConstants(expr)) {
            if (!eliminated.contains(c) && !isBound(c)) continue;
            final ParamDecl<?> p =
                    qeParams.computeIfAbsent(
                            List.of(params.size(), c.getType()),
                            k -> Decls.Param("__theta_qe_" + k.get(0), c.getType()));
            params.add(p);
            toParams.put(c, p.getRef());
        }
        if (params.isEmpty()) return expr;
        final var solver = qeSolvers.requestSolver();
        try {
            final Expr<BoolType> result =
                    solver.eliminateQuantifiers(
                            Exists(params, toParams.build().apply(expr)), "qe2");
            return hasQuantifier(result) ? expr : ExprUtils.simplify(result);
        } finally {
            qeSolvers.returnSolver(solver);
        }
    }

    private static boolean hasQuantifier(Expr<?> expr) {
        return expr instanceof QuantifiedExpr
                || expr.getOps().stream().anyMatch(SymbolicKeys::hasQuantifier);
    }

    private static int find(int[] parent, int i) {
        while (parent[i] != i) i = parent[i] = parent[parent[i]];
        return i;
    }

    private record Definition(Expr<BoolType> conjunct, Decl<?> decl, Expr<?> value) {}

    private static Definition definition(List<Expr<BoolType>> conjuncts, Set<Decl<?>> eliminated) {
        for (Expr<BoolType> conjunct : conjuncts) {
            if (!(conjunct instanceof EqExpr<?> eq)) continue;
            for (ConstDecl<?> c : ExprUtils.getConstants(eq)) {
                if (!eliminated.contains(c)) continue;
                Expr<?> solved = solve(eq.getLeftOp(), eq.getRightOp(), c);
                if (solved == null) solved = solve(eq.getRightOp(), eq.getLeftOp(), c);
                if (solved != null) return new Definition(conjunct, c, solved);
            }
        }
        return null;
    }

    // value = side, solved for c where side is c under additions, subtractions and negations
    @SuppressWarnings({"unchecked", "rawtypes"})
    private static Expr<?> solve(Expr<?> value, Expr<?> side, Decl<?> c) {
        if (ExprUtils.getConstants(value).contains(c)) return null;
        if (side instanceof RefExpr<?> ref && ref.getDecl().equals(c)) return value;
        if (side instanceof AddExpr<?> add) {
            Expr<?> withC = null;
            final List<Expr> others = new ArrayList<>();
            for (Expr<?> op : add.getOps()) {
                if (ExprUtils.getConstants(op).contains(c)) {
                    if (withC != null) return null;
                    withC = op;
                } else others.add(op);
            }
            if (withC == null) return null;
            Expr rest = value;
            for (Expr o : others) rest = AbstractExprs.Sub(rest, o);
            return solve(rest, withC, c);
        }
        if (side instanceof SubExpr<?> sub) {
            final boolean inLeft = ExprUtils.getConstants(sub.getLeftOp()).contains(c);
            final boolean inRight = ExprUtils.getConstants(sub.getRightOp()).contains(c);
            if (inLeft == inRight) return null;
            return inLeft
                    ? solve(
                            AbstractExprs.Add((Expr) value, (Expr) sub.getRightOp()),
                            sub.getLeftOp(),
                            c)
                    : solve(
                            AbstractExprs.Sub((Expr) sub.getLeftOp(), (Expr) value),
                            sub.getRightOp(),
                            c);
        }
        if (side instanceof NegExpr<?> neg) {
            return solve(AbstractExprs.Neg((Expr) value), neg.getOp(), c);
        }
        return null;
    }
}
