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

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class ExprSizeTest {

    private static final VarDecl<BoolType> VA = Var("a", Bool());
    private static final VarDecl<IntType> VB = Var("b", Int());

    private static final Expr<BoolType> A = VA.getRef();
    private static final Expr<IntType> B = VB.getRef();
    public Expr<Type> expr;
    public int expectedSize;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {True(), 1},
                    {A, 1},
                    {And(A, True()), 3},
                    {And(A, True(), False()), 4},
                    {And(A, And(True(), False())), 5},
                    {Add(B, Sub(Int(1), Int(2)), Int(3)), 6},
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(Expr<Type> expr, int expectedSize) {
        initExprSizeTest(expr, expectedSize);
        final int actualSize = ExprUtils.nodeCountSize(expr);
        assertEquals(expectedSize, actualSize);
    }

    public void initExprSizeTest(Expr<Type> expr, int expectedSize) {
        this.expr = expr;
        this.expectedSize = expectedSize;
    }
}
