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

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.stmt.Stmts.Skip;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.util.Arrays;
import java.util.Collection;
import java.util.Set;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class VarCollectorStmtVisitorTest {

    private static final VarDecl<BoolType> VA = Var("a", Bool());
    private static final VarDecl<IntType> VB = Var("b", Int());
    private static final VarDecl<IntType> VC = Var("d", Int());

    @Parameter(value = 0)
    public Stmt stmt;

    @Parameter(value = 1)
    public Set<VarDecl<?>> expectedVars;

    @Parameters
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {Skip(), of()},
                    {Havoc(VA), of(VA)},
                    {Havoc(VB), of(VB)},
                    {Assign(VB, Int(0)), of(VB)},
                    {Assign(VB, Add(VB.getRef(), VB.getRef())), of(VB)},
                    {Assign(VB, Add(VB.getRef(), VC.getRef())), of(VB, VC)},
                    {Assume(And(VA.getRef(), Eq(VB.getRef(), VC.getRef()))), of(VA, VB, VC)},
                });
    }

    @Test
    public void test() {
        final Set<VarDecl<?>> vars = StmtUtils.getVars(stmt);
        assertEquals(expectedVars, vars);
    }
}
