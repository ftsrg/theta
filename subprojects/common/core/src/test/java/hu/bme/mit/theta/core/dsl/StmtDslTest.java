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

import static hu.bme.mit.theta.core.stmt.Stmts.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class StmtDslTest {
    public String actual;
    public Stmt expected;
    public Collection<Decl<?>> decls;

    private static VarDecl<IntType> x = Decls.Var("x", Int());

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"assume true", Assume(True()), null},
                    {"x := x + 1", Assign(x, Add(x.getRef(), Int(1))), Collections.singleton(x)},
                    {"havoc x", Havoc(x), Collections.singleton(x)}
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(String actual, Stmt expected, Collection<Decl<?>> decls) {
        initStmtDslTest(actual, expected, decls);
        final CoreDslManager manager = new CoreDslManager();

        if (decls != null) {
            decls.forEach(decl -> manager.declare(decl));
        }

        Assertions.assertEquals(expected, manager.parseStmt(actual));
    }

    public void initStmtDslTest(String actual, Stmt expected, Collection<Decl<?>> decls) {
        this.actual = actual;
        this.expected = expected;
        this.decls = decls;
    }
}
