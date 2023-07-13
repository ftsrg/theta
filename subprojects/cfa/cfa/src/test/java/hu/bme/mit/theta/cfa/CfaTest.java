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
package hu.bme.mit.theta.cfa;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import org.junit.Test;

public class CfaTest {

    @Test(expected = IllegalArgumentException.class)
    public void testDuplicateLocationName() {
        CFA.Builder builder = CFA.builder();
        builder.createLoc("A");
        builder.createLoc("B");
        builder.createLoc("A");
    }

    @Test(expected = IllegalArgumentException.class)
    public void testDuplicateVarName() {
        CFA.Builder builder = CFA.builder();
        VarDecl<IntType> v1 = Decls.Var("x", IntExprs.Int());
        VarDecl<IntType> v2 = Decls.Var("x", IntExprs.Int());
        CFA.Loc init = builder.createLoc();
        CFA.Loc loc1 = builder.createLoc();
        CFA.Loc loc2 = builder.createLoc();
        builder.createEdge(init, loc1, Stmts.Havoc(v1));
        builder.createEdge(init, loc2, Stmts.Havoc(v2));
        builder.setInitLoc(init);
        builder.build();
    }
}
