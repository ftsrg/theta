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
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.Dereference;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * A {@link Dereference} is an application of the {@code deref} uninterpreted function, but --
 * unlike an ordinary {@code (f x)} whose {@code f} is a {@link ConstDecl} that {@code getConstants}
 * finds and the solver declares -- {@code deref} has no backing declaration in the expression, so
 * an SMT-LIB solver would emit {@code (deref …)} with no {@code (declare-fun deref …)} and be
 * rejected ("unknown symbol: deref"). The native Z3 API sidesteps this by minting a {@code
 * FuncDecl} per application; SMT-LIB cannot, and it additionally forbids redeclaring one name with
 * two signatures.
 *
 * <p>This gives every {@code deref} signature a canonical function {@link ConstDecl} -- cached, so
 * the same instance is used both when collecting the constants to declare and when transforming the
 * application, which matters because {@link ConstDecl} identity is reference equality. The solver's
 * existing constant-declaration machinery then declares and applies it exactly like any other
 * uninterpreted function, per distinct {@code (array, offset, index) -> result} signature.
 */
public final class SmtLibDereferenceDecls {

    private static final Map<List<Type>, ConstDecl<?>> CACHE = new ConcurrentHashMap<>();

    private SmtLibDereferenceDecls() {}

    /** The canonical {@code deref} function declaration for one dereference's signature. */
    public static ConstDecl<?> funcDecl(final Dereference<?, ?, ?> deref) {
        final Type arrayType = deref.getArray().getType();
        final Type offsetType = deref.getOffset().getType();
        final Type indexType = IntType.getInstance();
        final Type resultType = deref.getType();
        return CACHE.computeIfAbsent(
                List.of(arrayType, offsetType, indexType, resultType),
                key -> {
                    // Curried (array -> offset -> index -> result): the declaration transformer
                    // unfolds this into the flat parameter list `(arraySort offsetSort Int)`.
                    final FuncType<?, ?> funcType =
                            FuncType.of(
                                    arrayType,
                                    FuncType.of(offsetType, FuncType.of(indexType, resultType)));
                    final String name =
                            "deref_%s_%s_%s"
                                    .formatted(
                                            mangle(arrayType),
                                            mangle(offsetType),
                                            mangle(resultType));
                    return Decls.Const(name, funcType);
                });
    }

    /** The canonical function declarations of every dereference appearing in [expr]. */
    public static Set<ConstDecl<?>> collect(final Expr<?> expr) {
        final Set<ConstDecl<?>> result = new LinkedHashSet<>();
        collect(expr, result);
        return result;
    }

    private static void collect(final Expr<?> expr, final Set<ConstDecl<?>> result) {
        if (expr instanceof Dereference<?, ?, ?> deref) {
            result.add(funcDecl(deref));
        }
        expr.getOps().forEach(op -> collect(op, result));
    }

    /**
     * A sort's string form reduced to a legal SMT-LIB symbol fragment (e.g. {@code (_ BitVec 64)}
     * -> {@code BitVec64}).
     */
    private static String mangle(final Type type) {
        return type.toString().replaceAll("[^A-Za-z0-9]", "");
    }
}
