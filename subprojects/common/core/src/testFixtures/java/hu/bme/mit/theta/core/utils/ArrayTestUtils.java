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

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.type.arraytype.*;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import kotlin.Pair;

public class ArrayTestUtils {

    private ArrayTestUtils() {}

    public static Collection<?> BasicOperations() {

        final var c1 = Const("arr", ArrayType.of(Int(), Int()));

        return Arrays.asList(
                new Object[][] {
                    {
                        ArrayReadExpr.class,
                        Int(5),
                        ArrayReadExpr.of(ArrayWriteExpr.of(c1.getRef(), Int(0), Int(5)), Int(0))
                    },
                    {ArrayEqExpr.class, True(), ArrayEqExpr.of(c1.getRef(), c1.getRef())},
                    {ArrayNeqExpr.class, False(), ArrayNeqExpr.of(c1.getRef(), c1.getRef())},
                    {
                        ArrayReadExpr.class,
                        Int(5),
                        ArrayReadExpr.of(
                                ArrayLitExpr.of(List.of(), Int(5), ArrayType.of(Int(), Int())),
                                Int(42))
                    },
                    {
                        ArrayReadExpr.class,
                        Int(5),
                        ArrayReadExpr.of(
                                ArrayInitExpr.of(List.of(), Int(5), ArrayType.of(Int(), Int())),
                                Int(42))
                    },
                    {
                        ArrayReadExpr.class,
                        Int(3),
                        ArrayReadExpr.of(
                                ArrayLitExpr.of(
                                        List.of(new Pair<>(Int(42), Int(3))),
                                        Int(5),
                                        ArrayType.of(Int(), Int())),
                                Int(42))
                    },
                    {
                        ArrayReadExpr.class,
                        Int(3),
                        ArrayReadExpr.of(
                                ArrayInitExpr.of(
                                        List.of(new Pair<>(Int(42), Int(3))),
                                        Int(5),
                                        ArrayType.of(Int(), Int())),
                                Int(42))
                    },
                });
    }
}
