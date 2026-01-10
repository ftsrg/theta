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
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class WpStateTest {

    private static final VarDecl<IntType> VX = Var("x", Int());
    private static final VarDecl<IntType> VY = Var("y", Int());

    private static final Expr<IntType> X = VX.getRef();
    private static final Expr<IntType> Y = VY.getRef();

    private static final Expr<BoolType> TRUE = True();
    private static final Expr<BoolType> GEQ_X_1 = Geq(X, Int(1));
    private static final Expr<BoolType> GEQ_1_X = Geq(Int(1), X);
    private static final Expr<BoolType> GEQ_1_Y = Geq(Int(1), Y);
    private static final Expr<BoolType> GEQ_X_Y = Geq(X, Y);

    private static final Stmt ASSIGN_X_1 = Assign(VX, Int(1));
    private static final Stmt ASSIGN_Y_X = Assign(VY, X);
    public Expr<BoolType> expr;
    public Stmt stmt;
    public Expr<BoolType> expectedWp;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {TRUE, ASSIGN_X_1, TRUE},
                    {GEQ_X_1, ASSIGN_X_1, TRUE},
                    {GEQ_1_X, ASSIGN_X_1, TRUE},
                    {GEQ_1_Y, ASSIGN_X_1, GEQ_1_Y},
                    {GEQ_X_Y, ASSIGN_X_1, GEQ_1_Y},
                    {TRUE, ASSIGN_Y_X, TRUE},
                    {GEQ_X_1, ASSIGN_Y_X, GEQ_X_1},
                    {GEQ_1_X, ASSIGN_Y_X, GEQ_1_X},
                    {GEQ_1_Y, ASSIGN_Y_X, GEQ_1_X},
                    {GEQ_X_Y, ASSIGN_Y_X, TRUE},
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(Expr<BoolType> expr, Stmt stmt, Expr<BoolType> expectedWp) {
        initWpStateTest(expr, stmt, expectedWp);
        // Arrange
        final WpState state = WpState.of(expr);

        // Act
        final WpState actualState = state.wp(stmt);
        final Expr<BoolType> actualWp = ExprUtils.simplify(actualState.getExpr());

        // Assert
        assertEquals(expectedWp, actualWp);
    }

    public void initWpStateTest(Expr<BoolType> expr, Stmt stmt, Expr<BoolType> expectedWp) {
        this.expr = expr;
        this.stmt = stmt;
        this.expectedWp = expectedWp;
    }
}
