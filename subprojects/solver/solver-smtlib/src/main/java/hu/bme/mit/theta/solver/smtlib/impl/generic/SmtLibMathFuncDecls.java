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
 * One canonical function {@link ConstDecl} per math function and sort, as {@link
 * SmtLibDereferenceDecls} does for {@code deref}: the application has no declaration of its own,
 * and SMT-LIB forbids one name with two signatures.
 */
public final class SmtLibMathFuncDecls {

    private record Key(FpMathFuncExpr.Function function, FpType type) {}

    private static final Map<Key, ConstDecl<?>> CACHE = new ConcurrentHashMap<>();
    private static final Map<ConstDecl<?>, FpMathFuncExpr.Function> FUNCTIONS =
            new ConcurrentHashMap<>();

    private SmtLibMathFuncDecls() {}

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

    public static Optional<FpMathFuncExpr.Function> functionOf(final ConstDecl<?> decl) {
        return Optional.ofNullable(FUNCTIONS.get(decl));
    }

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
