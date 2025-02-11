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

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.QuantifiedExpr;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class ExpressionUtils {

    private static Stream<Expr<?>> getWithAllOps(Expr<?> e) {
        if (e instanceof QuantifiedExpr || e instanceof FuncAppExpr) {
            return Stream.of(
                    e); // we don't want their body to be unwrapped, as they contain ParamDecls
        }
        return Stream.concat(Stream.of(e), e.getOps().stream());
    }

    public static Map<String, ? extends Expr<?>> AllExpressions() {
        return Stream.of(
                        BvTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[2]),
                        BvTestUtils.BitvectorOperations().stream().map(o -> ((Object[]) o)[2]),
                        BvTestUtils.RelationalOperations().stream().map(o -> ((Object[]) o)[2]),
                        FpTestUtils.GetOperations().map(o -> ((Object[]) o)[2]),
                        IntTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[2]),
                        RatTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[2]),
                        BoolTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[2]),
                        ArrayTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[2]),
                        FuncTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[2]),
                        BvTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[1]),
                        BvTestUtils.BitvectorOperations().stream().map(o -> ((Object[]) o)[1]),
                        BvTestUtils.RelationalOperations().stream().map(o -> ((Object[]) o)[1]),
                        FpTestUtils.GetOperations().map(o -> ((Object[]) o)[1]),
                        IntTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[1]),
                        RatTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[1]),
                        BoolTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[1]),
                        ArrayTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[1]),
                        FuncTestUtils.BasicOperations().stream().map(o -> ((Object[]) o)[1]))
                .reduce(Stream::concat)
                .get()
                .map(o -> (Expr<?>) o)
                .flatMap(ExpressionUtils::getWithAllOps)
                .collect(
                        Collectors.toMap(
                                o -> o.getClass().getSimpleName(), o -> o, (expr, expr2) -> expr2));
    }
}
