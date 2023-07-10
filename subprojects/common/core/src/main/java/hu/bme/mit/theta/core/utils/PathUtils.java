/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;

import java.util.Collection;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;

/**
 * Utility functions related to paths.
 */
public class PathUtils {

    private PathUtils() {
    }

    ////

    public static VarIndexing countPrimes(final Expr<?> expr) {
        return PrimeCounter.countPrimes(expr);
    }

    ////

    /**
     * Transform an expression by substituting variables with indexed constants.
     *
     * @param expr     Original expression
     * @param indexing Indexing for the variables
     * @return Transformed expression
     */
    public static <T extends Type> Expr<T> unfold(final Expr<T> expr, final VarIndexing indexing) {
        checkNotNull(expr);
        checkNotNull(indexing);
        final UnfoldHelper helper = new UnfoldHelper(indexing);
        return helper.unfold(expr, 0);
    }

    /**
     * Transform an expression by substituting variables with indexed constants.
     *
     * @param expr Original expression
     * @param i    Index
     * @return Transformed expression
     */
    public static <T extends Type> Expr<T> unfold(final Expr<T> expr, final int i) {
        checkArgument(i >= 0);
        return unfold(expr, VarIndexingFactory.indexing(i));
    }

    /**
     * Transform an expression by substituting indexed constants with variables.
     *
     * @param expr     Original expression
     * @param indexing Indexing for the variables
     * @return Transformed expression
     */
    public static <T extends Type> Expr<T> foldin(final Expr<T> expr, final VarIndexing indexing) {
        checkNotNull(expr);
        checkNotNull(indexing);
        final FoldinHelper helper = new FoldinHelper(indexing);
        return helper.foldin(expr);
    }

    /**
     * Transform an expression by substituting indexed constants with variables.
     *
     * @param expr Original expression
     * @param i    Index
     * @return Transformed expression
     */
    public static <T extends Type> Expr<T> foldin(final Expr<T> expr, final int i) {
        checkArgument(i >= 0);
        return foldin(expr, VarIndexingFactory.indexing(i));
    }

    /**
     * Extract values from a model for a given indexing. If you know the set of variables to be
     * extracted, use that overload because it is more efficient.
     *
     * @param model    Model
     * @param indexing Indexing
     * @return Values
     */
    public static Valuation extractValuation(final Valuation model, final VarIndexing indexing) {
        final ImmutableValuation.Builder builder = ImmutableValuation.builder();
        for (final Decl<?> decl : model.getDecls()) {
            if (decl instanceof IndexedConstDecl) {
                final IndexedConstDecl<?> indexedConstDecl = (IndexedConstDecl<?>) decl;
                final VarDecl<?> varDecl = indexedConstDecl.getVarDecl();
                if (indexedConstDecl.getIndex() == indexing.get(varDecl)) {
                    final LitExpr<?> value = model.eval(indexedConstDecl).get();
                    builder.put(varDecl, value);
                }
            }
        }
        return builder.build();
    }

    /**
     * Extract values from a model for a given index. If you know the set of variables to be
     * extracted, use that overload because it is more efficient.
     *
     * @param model Model
     * @param i     Index
     * @return Values
     */
    public static Valuation extractValuation(final Valuation model, final int i) {
        checkArgument(i >= 0);
        return extractValuation(model, VarIndexingFactory.indexing(i));
    }

    /**
     * Extract values from a model for a given indexing and given variables. If a variable has no
     * value in the model, it will not be included in the return value.
     *
     * @param model    Model
     * @param indexing Indexing
     * @return Values
     */
    public static Valuation extractValuation(final Valuation model, final VarIndexing indexing,
                                             final Collection<? extends VarDecl<?>> varDecls) {
        final ImmutableValuation.Builder builder = ImmutableValuation.builder();
        for (final VarDecl<?> varDecl : varDecls) {
            final int index = indexing.get(varDecl);
            final IndexedConstDecl<?> constDecl = varDecl.getConstDecl(index);
            final Optional<? extends LitExpr<?>> eval = model.eval(constDecl);
            if (eval.isPresent()) {
                builder.put(varDecl, eval.get());
            }
        }
        return builder.build();
    }

    /**
     * Extract values from a model for a given index and given variables. If a variable has no value
     * in the model, it will not be included in the return value.
     *
     * @param model Model
     * @param i     Index
     * @return Values
     */
    public static Valuation extractValuation(final Valuation model, final int i,
                                             final Collection<? extends VarDecl<?>> varDecls) {
        checkArgument(i >= 0);
        return extractValuation(model, VarIndexingFactory.indexing(i), varDecls);
    }

    ////

    private static final class UnfoldHelper {

        private final VarIndexing indexing;

        private UnfoldHelper(final VarIndexing indexing) {
            this.indexing = indexing;
        }

        public <T extends Type> Expr<T> unfold(final Expr<T> expr, final int offset) {
            if (expr instanceof RefExpr) {
                final RefExpr<T> ref = (RefExpr<T>) expr;
                final Decl<T> decl = ref.getDecl();
                if (decl instanceof VarDecl) {
                    final VarDecl<T> varDecl = (VarDecl<T>) decl;
                    final int index = indexing.get(varDecl) + offset;
                    final ConstDecl<T> constDecl = varDecl.getConstDecl(index);
                    final RefExpr<T> refExpr = constDecl.getRef();
                    return refExpr;
                }
            }

            if (expr instanceof PrimeExpr) {
                final PrimeExpr<T> prime = (PrimeExpr<T>) expr;
                final Expr<T> op = prime.getOp();
                return unfold(op, offset + 1);
            }

            return expr.map(op -> unfold(op, offset));
        }
    }

    ////

    private static final class FoldinHelper {

        private final VarIndexing indexing;

        private FoldinHelper(final VarIndexing indexing) {
            this.indexing = indexing;
        }

        public <T extends Type> Expr<T> foldin(final Expr<T> expr) {
            if (expr instanceof RefExpr) {
                final RefExpr<T> ref = (RefExpr<T>) expr;
                final Decl<T> decl = ref.getDecl();
                if (decl instanceof IndexedConstDecl) {
                    final IndexedConstDecl<T> constDecl = (IndexedConstDecl<T>) decl;
                    final VarDecl<T> varDecl = constDecl.getVarDecl();
                    final int index = constDecl.getIndex();
                    final int nPrimes = index - indexing.get(varDecl);
                    checkArgument(nPrimes >= 0, "Indexing mismatch on declaration");
                    final Expr<T> varRef = varDecl.getRef();
                    if (nPrimes == 0) {
                        return varRef;
                    } else {
                        return Prime(varRef, nPrimes);
                    }
                }
            }

            return expr.map(this::foldin);
        }
    }

}
