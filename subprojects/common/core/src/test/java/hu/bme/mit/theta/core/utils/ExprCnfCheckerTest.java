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
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class ExprCnfCheckerTest {

    private static final Expr<BoolType> A = Const("a", Bool()).getRef();
    private static final Expr<BoolType> B = Const("b", Bool()).getRef();
    private static final Expr<BoolType> C = Const("c", Bool()).getRef();

    @Parameter(value = 0)
    public Expr<BoolType> expr;

    @Parameter(value = 1)
    public boolean expectedResult;

    @Parameters
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

    @Test
    public void test() {
        Assert.assertEquals(expectedResult, isExprCnf(expr));
    }
}
