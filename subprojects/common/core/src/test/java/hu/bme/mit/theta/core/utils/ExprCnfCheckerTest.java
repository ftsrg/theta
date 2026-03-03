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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.utils.ExprUtils.isExprCnf;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class ExprCnfCheckerTest {

    private static final Expr<BoolType> A = Const("a", Bool()).getRef();
    private static final Expr<BoolType> B = Const("b", Bool()).getRef();
    private static final Expr<BoolType> C = Const("c", Bool()).getRef();
    public Expr<BoolType> expr;
    public boolean expectedResult;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    // A
                    {A, true},
                    // !A
                    {Not(A), true},
                    // !A or B or !C
                    {Or(Not(A), B, Not(C)), true},
                    // !A and B and !C
                    {And(Not(A), B, Not(C)), true},
                    // !A and (B and !C)
                    {And(Not(A), And(B, Not(C))), true},
                    // !A and (B or !C)
                    {And(Not(A), Or(B, Not(C))), true},
                    // !!A
                    {Not(Not(A)), false},
                    // !A and B and !C
                    {And(Not(A), B, Not(C)), true},
                    // !A or (B and !C)
                    {Or(Not(A), And(B, Not(C))), false},
                    // !(A and B)
                    {Not(And(A, B)), false},
                    // !(A or B)
                    {Not(Or(A, B)), false},
                    // A -> B
                    {Imply(A, B), false},
                    // A <-> B
                    {Iff(A, B), false},
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(Expr<BoolType> expr, boolean expectedResult) {
        initExprCnfCheckerTest(expr, expectedResult);
        Assertions.assertEquals(expectedResult, isExprCnf(expr));
    }

    public void initExprCnfCheckerTest(Expr<BoolType> expr, boolean expectedResult) {
        this.expr = expr;
        this.expectedResult = expectedResult;
    }
}
