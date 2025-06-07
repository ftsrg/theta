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
package hu.bme.mit.theta.core.utils;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.*;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.utils.IndexedVars.Builder;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

/** Utility functions related to expressions. */
public final class ExprUtils {

    private static final ExprSimplifier exprSimplifier = ExprSimplifier.create();

    private ExprUtils() {}

    /**
     * Collect atoms from a Boolean expression into a given collection.
     *
     * @param expr Expression
     * @param collectTo Collection where the atoms should be put
     */
    public static void collectAtoms(
            final Expr<BoolType> expr, final Collection<Expr<BoolType>> collectTo) {
        ExprAtomCollector.collectAtoms(expr, collectTo);
    }

    /**
     * Collect atoms from a Boolean expression.
     *
     * @param expr Expression
     * @return Set of atoms
     */
    public static Set<Expr<BoolType>> getAtoms(final Expr<BoolType> expr) {
        final Set<Expr<BoolType>> atoms = Containers.createSet();
        collectAtoms(expr, atoms);
        return atoms;
    }

    /**
     * Check if an expression is in CNF form.
     *
     * @param expr Expression
     * @return True, if the expression is in CNF
     */
    public static boolean isExprCnf(final Expr<BoolType> expr) {
        return ExprCnfChecker.isExprCnf(expr);
    }

    /**
     * Transform an expression into an equisatisfiable CNF form.
     *
     * @param expr Original expression
     * @return Transformed expression
     */
    public static Expr<BoolType> transformEquiSatCnf(final Expr<BoolType> expr) {
        return new ExprCnfTransformer().transformEquiSat(expr);
    }

    public static OrExpr toDnf(final Expr<BoolType> expr) {
        if (expr instanceof OrExpr) {
            var ops = expr.getOps().stream().map(it -> toDnf((Expr<BoolType>) it)).toList();
            return OrExpr.of(ops.stream().flatMap(or -> or.getOps().stream()).toList());
        } else {
            return OrExpr.of(List.of(expr));
        }
    }

    /**
     * Get conjuncts of an expression.
     *
     * @param expr Expression
     * @return Collection of conjuncts
     */
    public static Collection<Expr<BoolType>> getConjuncts(final Expr<BoolType> expr) {
        checkNotNull(expr);

        if (expr instanceof AndExpr) {
            final AndExpr andExpr = (AndExpr) expr;
            return andExpr.getOps().stream()
                    .map(ExprUtils::getConjuncts)
                    .flatMap(Collection::stream)
                    .collect(Collectors.toSet());
        } else {
            return Collections.singleton(expr);
        }
    }

    /**
     * Collect params of an expression into a given collection.
     *
     * @param expr Expression
     * @param collectTo Collection where the params should be put
     */
    public static void collectParams(final Expr<?> expr, final Collection<ParamDecl<?>> collectTo) {
        if (expr instanceof RefExpr<?> refExpr) {
            final Decl<?> decl = refExpr.getDecl();
            if (decl instanceof ParamDecl<?> param) {
                collectTo.add(param);
                return;
            }
        }

        if (expr instanceof ForallExpr forall) {
            Set<ParamDecl<?>> params = new LinkedHashSet<>(getParams(forall.getOp()));
            forall.getParamDecls().forEach(params::remove);
            collectTo.addAll(params);
        } else if (expr instanceof ExistsExpr exists) {
            Set<ParamDecl<?>> params = new LinkedHashSet<>(getParams(exists.getOp()));
            exists.getParamDecls().forEach(params::remove);
            collectTo.addAll(params);
        } else {
            expr.getOps().forEach(op -> collectParams(op, collectTo));
        }
    }

    /**
     * Collect params from expressions into a given collection.
     *
     * @param exprs Expressions
     * @param collectTo Collection where the variables should be put
     */
    public static void collectParams(
            final Iterable<? extends Expr<?>> exprs, final Collection<ParamDecl<?>> collectTo) {
        exprs.forEach(e -> collectParams(e, collectTo));
    }

    /**
     * Get variables of an expression.
     *
     * @param expr Expression
     * @return Set of variables appearing in the expression
     */
    public static Set<ParamDecl<?>> getParams(final Expr<?> expr) {
        final Set<ParamDecl<?>> vars = Containers.createSet();
        collectParams(expr, vars);
        return vars;
    }

    /**
     * Get variables of expressions.
     *
     * @param exprs Expressions
     * @return Set of variables appearing in the expressions
     */
    public static Set<ParamDecl<?>> getParams(final Iterable<? extends Expr<?>> exprs) {
        final Set<ParamDecl<?>> vars = Containers.createSet();
        collectParams(exprs, vars);
        return vars;
    }

    /**
     * Collect variables of an expression into a given collection.
     *
     * @param expr Expression
     * @param collectTo Collection where the variables should be put
     */
    public static void collectVars(final Expr<?> expr, final Collection<VarDecl<?>> collectTo) {
        if (expr instanceof RefExpr) {
            final RefExpr<?> refExpr = (RefExpr<?>) expr;
            final Decl<?> decl = refExpr.getDecl();
            if (decl instanceof VarDecl) {
                final VarDecl<?> varDecl = (VarDecl<?>) decl;
                collectTo.add(varDecl);
                return;
            }
        }
        expr.getOps().forEach(op -> collectVars(op, collectTo));
    }

    /**
     * Collect variables from expressions into a given collection.
     *
     * @param exprs Expressions
     * @param collectTo Collection where the variables should be put
     */
    public static void collectVars(
            final Iterable<? extends Expr<?>> exprs, final Collection<VarDecl<?>> collectTo) {
        exprs.forEach(e -> collectVars(e, collectTo));
    }

    /**
     * Get variables of an expression.
     *
     * @param expr Expression
     * @return Set of variables appearing in the expression
     */
    public static Set<VarDecl<?>> getVars(final Expr<?> expr) {
        final Set<VarDecl<?>> vars = Containers.createSet();
        collectVars(expr, vars);
        return vars;
    }

    /**
     * Get variables of expressions.
     *
     * @param exprs Expressions
     * @return Set of variables appearing in the expressions
     */
    public static Set<VarDecl<?>> getVars(final Iterable<? extends Expr<?>> exprs) {
        final Set<VarDecl<?>> vars = Containers.createSet();
        collectVars(exprs, vars);
        return vars;
    }

    /**
     * Collect indexed constants of an expression into a given collection.
     *
     * @param expr Expression
     * @param collectTo Collection where the constants should be put
     */
    public static void collectIndexedConstants(
            final Expr<?> expr, final Collection<IndexedConstDecl<?>> collectTo) {
        if (expr instanceof RefExpr) {
            final RefExpr<?> refExpr = (RefExpr<?>) expr;
            final Decl<?> decl = refExpr.getDecl();
            if (decl instanceof IndexedConstDecl<?>) {
                final IndexedConstDecl<?> constDecl = (IndexedConstDecl<?>) decl;
                collectTo.add(constDecl);
                return;
            }
        }
        expr.getOps().forEach(op -> collectIndexedConstants(op, collectTo));
    }

    /**
     * Collect indexed constants from expressions into a given collection.
     *
     * @param exprs Expressions
     * @param collectTo Collection where the constants should be put
     */
    public static void collectIndexedConstants(
            final Iterable<? extends Expr<?>> exprs,
            final Collection<IndexedConstDecl<?>> collectTo) {
        exprs.forEach(e -> collectIndexedConstants(e, collectTo));
    }

    /**
     * Get indexed constants of an expression.
     *
     * @param expr Expression
     * @return Set of constants appearing in the expression
     */
    public static Set<IndexedConstDecl<?>> getIndexedConstants(final Expr<?> expr) {
        final Set<IndexedConstDecl<?>> consts = new HashSet<>();
        collectIndexedConstants(expr, consts);
        return consts;
    }

    /**
     * Get indexed constants of expressions.
     *
     * @param exprs Expressions
     * @return Set of constants appearing in the expressions
     */
    public static Set<IndexedConstDecl<?>> getIndexedConstants(
            final Iterable<? extends Expr<?>> exprs) {
        final Set<IndexedConstDecl<?>> consts = new HashSet<>();
        collectIndexedConstants(exprs, consts);
        return consts;
    }

    /**
     * Collect constants of an expression into a given collection.
     *
     * @param expr Expression
     * @param collectTo Collection where the constants should be put
     */
    public static void collectConstants(
            final Expr<?> expr, final Collection<ConstDecl<?>> collectTo) {
        if (expr instanceof RefExpr) {
            final RefExpr<?> refExpr = (RefExpr<?>) expr;
            final Decl<?> decl = refExpr.getDecl();
            if (decl instanceof ConstDecl) {
                final ConstDecl<?> constDecl = (ConstDecl<?>) decl;
                collectTo.add(constDecl);
                return;
            }
        }
        expr.getOps().forEach(op -> collectConstants(op, collectTo));
    }

    /**
     * Collect constants from expressions into a given collection.
     *
     * @param exprs Expressions
     * @param collectTo Collection where the constants should be put
     */
    public static void collectConstants(
            final Iterable<? extends Expr<?>> exprs, final Collection<ConstDecl<?>> collectTo) {
        exprs.forEach(e -> collectConstants(e, collectTo));
    }

    /**
     * Get constants of an expression.
     *
     * @param expr Expression
     * @return Set of constants appearing in the expression
     */
    public static Set<ConstDecl<?>> getConstants(final Expr<?> expr) {
        final Set<ConstDecl<?>> consts = new HashSet<>();
        collectConstants(expr, consts);
        return consts;
    }

    /**
     * Get constants of expressions.
     *
     * @param exprs Expressions
     * @return Set of constants appearing in the expressions
     */
    public static Set<ConstDecl<?>> getConstants(final Iterable<? extends Expr<?>> exprs) {
        final Set<ConstDecl<?>> consts = new HashSet<>();
        collectConstants(exprs, consts);
        return consts;
    }

    /**
     * Get indexed variables of an expression.
     *
     * @param expr Expression
     * @return Indexed variables appearing in the expression
     */
    public static IndexedVars getVarsIndexed(final Expr<?> expr) {
        final Builder builder = IndexedVars.builder();
        ExprIndexedVarCollector.collectIndexedVars(expr, builder);
        return builder.build();
    }

    /**
     * Get indexed variables of expressions
     *
     * @param exprs Expressions
     * @return Indexed variables appearing in the expressions
     */
    public static IndexedVars getVarsIndexed(final Iterable<? extends Expr<?>> exprs) {
        final Builder builder = IndexedVars.builder();
        exprs.forEach(e -> ExprIndexedVarCollector.collectIndexedVars(e, builder));
        return builder.build();
    }

    /**
     * Transform expression into an equivalent new expression without if-then-else constructs.
     *
     * @param expr Original expression
     * @return Transformed expression
     */
    public static Expr<BoolType> eliminateIte(final Expr<BoolType> expr) {
        return ExprIteEliminator.eliminateIte(expr);
    }

    /**
     * Simplify expression and substitute the valuation.
     *
     * @param expr Original expression
     * @param val Valuation
     * @return Simplified expression
     */
    public static <ExprType extends Type> Expr<ExprType> simplify(
            final Expr<ExprType> expr, final Valuation val) {
        return exprSimplifier.simplify(expr, val);
    }

    /**
     * Simplify expression.
     *
     * @param expr Original expression
     * @return Simplified expression
     */
    public static <ExprType extends Type> Expr<ExprType> simplify(final Expr<ExprType> expr) {
        return simplify(expr, ImmutableValuation.empty());
    }

    /**
     * Simplify a list of expressions.
     *
     * @param exprs Original expressions
     * @return Simplified expressions
     */
    public static List<Expr<?>> simplifyAll(final List<? extends Expr<?>> exprs) {
        final List<Expr<?>> simplifiedArgs = new ArrayList<>();
        for (final Expr<?> expr : exprs) {
            final Expr<?> simplifiedArg = simplify(expr);
            simplifiedArgs.add(simplifiedArg);
        }
        return simplifiedArgs;
    }

    /**
     * Return the canonical form of an expression.
     *
     * @param expr Original expression
     * @return Canonical form
     */
    public static <ExprType extends Type> Expr<ExprType> canonize(final Expr<ExprType> expr) {
        return ExprCanonizer.canonize(expr);
    }

    /**
     * Return the canonical form of a list of expressions.
     *
     * @param exprs Original expressions
     * @return Canonical forms
     */
    public static List<Expr<?>> canonizeAll(final List<? extends Expr<?>> exprs) {
        final List<Expr<?>> canonizedArgs = new ArrayList<>();
        for (final Expr<?> expr : exprs) {
            final Expr<?> canonizedArg = canonize(expr);
            canonizedArgs.add(canonizedArg);
        }
        return canonizedArgs;
    }

    /**
     * Reverses the given expression (swaps primed variables with unprimed variables and
     * vice-versa). Also works if variables can have multiple primes.
     *
     * @param expr Original expression
     * @return Reversed form
     */
    public static <ExprType extends Type> Expr<ExprType> reverse(
            final Expr<ExprType> expr, final VarIndexing indexing) {
        return new ExprReverser(indexing).reverse(expr);
    }

    /**
     * Reverses the given expression (swaps primed variables with unprimed variables and
     * vice-versa).
     *
     * @param expr Original expression
     * @return Reversed form
     */
    public static <ExprType extends Type> Expr<ExprType> reverse(final Expr<ExprType> expr) {
        return new ExprReverser(VarIndexingFactory.indexing(1)).reverse(expr);
    }

    /**
     * Transform an expression into a ponated one.
     *
     * @param expr Original expression
     * @return Transformed expression
     */
    public static Expr<BoolType> ponate(final Expr<BoolType> expr) {
        if (expr instanceof NotExpr) {
            final NotExpr notExpr = (NotExpr) expr;
            return ponate(notExpr.getOp());
        } else {
            return expr;
        }
    }

    /**
     * Transform an expression by universally quantifying certain variables.
     *
     * @param expr Original expression
     * @param mapping Quantifying
     * @return Transformed expression
     */
    public static <T extends Type> Expr<T> close(
            final Expr<T> expr, final Map<VarDecl<?>, ParamDecl<?>> mapping) {
        return ExprCloser.close(expr, mapping);
    }

    /**
     * Transform an expression by applying primes to an expression based on an indexing.
     *
     * @param expr Original expression
     * @param indexing Indexing
     * @return Transformed expression
     */
    public static <T extends Type> Expr<T> applyPrimes(
            final Expr<T> expr, final VarIndexing indexing) {
        return ExprPrimeApplier.applyPrimes(expr, indexing);
    }

    /**
     * Get the size of an expression by counting the nodes in its tree representation.
     *
     * @param expr Expression
     * @return Node count
     */
    public static int nodeCountSize(final Expr<?> expr) {
        return 1 + expr.getOps().stream().map(ExprUtils::nodeCountSize).reduce(0, (x, y) -> x + y);
    }

    /**
     * Change fixed subexpressions using a lookup
     *
     * @param expr the expr to change subexpressions in
     * @param lookup the lookup mapping subexpression to replacements
     * @return the changed expression
     */
    public static <T extends Type> Expr<T> changeSubexpr(
            Expr<T> expr, Map<Expr<?>, Expr<?>> lookup) {
        if (lookup.containsKey(expr)) {
            return cast(lookup.get(expr), expr.getType());
        } else {
            return expr.map(e -> changeSubexpr(e, lookup));
        }
    }

    public static <T extends Type> Expr<T> changeDecls(
            Expr<T> expr, Map<? extends Decl<?>, ? extends Decl<?>> lookup) {
        return changeSubexpr(
                expr,
                lookup.entrySet().stream()
                        .map(entry -> Map.entry(entry.getKey().getRef(), entry.getValue().getRef()))
                        .collect(Collectors.toMap(Entry::getKey, Entry::getValue)));
    }

    /** Extracts function and its arguments from a nested expression */
    public static Tuple2<Expr<?>, List<Expr<?>>> extractFuncAndArgs(final FuncAppExpr<?, ?> expr) {
        final Expr<?> func = expr.getFunc();
        final Expr<?> arg = expr.getParam();
        if (func instanceof FuncAppExpr) {
            final FuncAppExpr<?, ?> funcApp = (FuncAppExpr<?, ?>) func;
            final Tuple2<Expr<?>, List<Expr<?>>> funcAndArgs = extractFuncAndArgs(funcApp);
            final Expr<?> resFunc = funcAndArgs.get1();
            final List<Expr<?>> args = funcAndArgs.get2();
            final List<Expr<?>> resArgs =
                    ImmutableList.<Expr<?>>builder().addAll(args).add(arg).build();
            return Tuple2.of(resFunc, resArgs);
        } else {
            return Tuple2.of(func, ImmutableList.of(arg));
        }
    }
}
