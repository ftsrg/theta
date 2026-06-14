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
package hu.bme.mit.theta.core.dsl;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class StmtWriteTest {

    private static final VarDecl<IntType> VX = Decls.Var("x", IntExprs.Int());
    public Stmt actual;
    public String expected;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {Stmts.Havoc(VX), "havoc x"},
                    {Stmts.Assume(BoolExprs.False()), "assume false"},
                    {Stmts.Assign(VX, IntExprs.Int(1)), "x := 1"},
                    {Stmts.Skip(), "skip"},
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(Stmt actual, String expected) {
        initStmtWriteTest(actual, expected);
        final CoreDslManager manager = new CoreDslManager();
        Assertions.assertEquals(expected, manager.writeStmt(actual));
    }

    public void initStmtWriteTest(Stmt actual, String expected) {
        this.actual = actual;
        this.expected = expected;
    }
}
