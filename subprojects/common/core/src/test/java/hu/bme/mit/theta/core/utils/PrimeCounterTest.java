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
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static java.util.Arrays.asList;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.CoreDslManager;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class PrimeCounterTest {
    public String exprString;
    public int nPrimesOnX;
    public int nPrimesOnY;

    public static Collection<Object[]> data() {
        return asList(
                new Object[][] {
                    {"true", 0, 0},
                    {"(true)'", 0, 0},
                    {"x", 0, 0},
                    {"not x'", 1, 0},
                    {"x''", 2, 0},
                    {"x' and y", 1, 0},
                    {"(x imply y)'", 1, 1},
                    {"(x' iff y)'", 2, 1},
                    {"a", 0, 0},
                    {"a'", 0, 0},
                    {"x' and a", 1, 0},
                    {"(x' or a)'", 2, 0}
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(String exprString, int nPrimesOnX, int nPrimesOnY) {
        initPrimeCounterTest(exprString, nPrimesOnX, nPrimesOnY);
        // Arrange
        final ConstDecl<BoolType> a = Const("a", Bool());
        final VarDecl<BoolType> x = Var("x", Bool());
        final VarDecl<BoolType> y = Var("y", Bool());

        final CoreDslManager manager = new CoreDslManager();
        manager.declare(a);
        manager.declare(x);
        manager.declare(y);

        final Expr<?> expr = manager.parseExpr(exprString);

        // Act
        final VarIndexing indexing = PathUtils.countPrimes(expr);

        // Assert
        assertEquals(nPrimesOnX, indexing.get(x));
        assertEquals(nPrimesOnY, indexing.get(y));
    }

    public void initPrimeCounterTest(String exprString, int nPrimesOnX, int nPrimesOnY) {
        this.exprString = exprString;
        this.nPrimesOnX = nPrimesOnX;
        this.nPrimesOnY = nPrimesOnY;
    }
}
