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
package hu.bme.mit.theta.solver.smtlib.impl.generic;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.fptype.FpMathFuncExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * An {@link FpMathFuncExpr} is an application of an uninterpreted function, but, like {@code deref}
 * (see {@link SmtLibDereferenceDecls}), it has no backing declaration in the expression, and
 * SMT-LIB forbids declaring one name with two signatures. This gives every function and sort one
 * canonical function {@link ConstDecl}, cached so the same instance is used when collecting the
 * constants to declare, when transforming the application, and when mapping a solver's term back to
 * it.
 */
public final class SmtLibMathFuncDecls {

    private record Key(FpMathFuncExpr.Function function, FpType type) {}

    private static final Map<Key, ConstDecl<?>> CACHE = new ConcurrentHashMap<>();
    private static final Map<ConstDecl<?>, FpMathFuncExpr.Function> FUNCTIONS =
            new ConcurrentHashMap<>();

    private SmtLibMathFuncDecls() {}

    /** The canonical function declaration of one application's function and sort. */
    public static ConstDecl<?> funcDecl(final FpMathFuncExpr expr) {
        final FpType type = expr.getType();
        return CACHE.computeIfAbsent(
                new Key(expr.getFunction(), type),
                key -> {
                    final ConstDecl<?> decl =
                            Decls.Const(
                                    "%s_%d_%d"
                                            .formatted(
                                                    key.function().getLabel(),
                                                    type.getExponent(),
                                                    type.getSignificand()),
                                    FuncType.of(type, type));
                    FUNCTIONS.put(decl, key.function());
                    return decl;
                });
    }

    /** The function a canonical declaration stands for, if it is one. */
    public static Optional<FpMathFuncExpr.Function> functionOf(final ConstDecl<?> decl) {
        return Optional.ofNullable(FUNCTIONS.get(decl));
    }

    /** The canonical function declarations of every math function applied in [expr]. */
    public static Set<ConstDecl<?>> collect(final Expr<?> expr) {
        final Set<ConstDecl<?>> result = new LinkedHashSet<>();
        collect(expr, result);
        return result;
    }

    private static void collect(final Expr<?> expr, final Set<ConstDecl<?>> result) {
        if (expr instanceof FpMathFuncExpr app) {
            result.add(funcDecl(app));
        }
        expr.getOps().forEach(op -> collect(op, result));
    }
}
