/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.inttype.IntType;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.stmt.Stmts.*;

@RunWith(Parameterized.class)
public class StmtDslTest {

    @Parameterized.Parameter(value = 0)
    public String actual;

    @Parameterized.Parameter(value = 1)
    public Stmt expected;

    @Parameterized.Parameter(value = 2)
    public Collection<Decl<?>> decls;

    private static VarDecl<IntType> x = Decls.Var("x", Int());

    @Parameterized.Parameters
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{

                {"assume true", Assume(True()), null},

                {"x := x + 1", Assign(x, Add(x.getRef(), Int(1))), Collections.singleton(x)},

                {"havoc x", Havoc(x), Collections.singleton(x)}

        });
    }

    @Test
    public void test() {
        final CoreDslManager manager = new CoreDslManager();

        if (decls != null) {
            decls.forEach(decl -> manager.declare(decl));
        }

        Assert.assertEquals(expected, manager.parseStmt(actual));
    }
}
