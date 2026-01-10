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
package hu.bme.mit.theta.analysis.pred;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class PredOrdTest {

    private final VarDecl<IntType> VX = Decls.Var("x", Int());

    private final PredOrd ord = PredOrd.create(Z3LegacySolverFactory.getInstance().createSolver());

    PredState sb = PredState.of(False());
    PredState s1 = PredState.of(Gt(VX.getRef(), Int(1)));
    PredState s2 = PredState.of(Gt(VX.getRef(), Int(0)));
    PredState s3 = PredState.of(Lt(VX.getRef(), Int(5)));
    PredState st = PredState.of();

    @Test
    public void testBottom() {
        Assertions.assertTrue(sb.isBottom());
        Assertions.assertFalse(s1.isBottom());
        Assertions.assertFalse(s2.isBottom());
        Assertions.assertFalse(s3.isBottom());
        Assertions.assertFalse(st.isBottom());
    }

    @Test
    public void testLeq() {
        Assertions.assertTrue(ord.isLeq(sb, sb));
        Assertions.assertTrue(ord.isLeq(sb, s1));
        Assertions.assertTrue(ord.isLeq(sb, s2));
        Assertions.assertTrue(ord.isLeq(sb, s3));
        Assertions.assertTrue(ord.isLeq(sb, st));

        Assertions.assertFalse(ord.isLeq(s1, sb));
        Assertions.assertTrue(ord.isLeq(s1, s1));
        Assertions.assertTrue(ord.isLeq(s1, s2));
        Assertions.assertFalse(ord.isLeq(s1, s3));
        Assertions.assertTrue(ord.isLeq(s1, st));

        Assertions.assertFalse(ord.isLeq(s2, sb));
        Assertions.assertFalse(ord.isLeq(s2, s1));
        Assertions.assertTrue(ord.isLeq(s2, s2));
        Assertions.assertFalse(ord.isLeq(s2, s3));
        Assertions.assertTrue(ord.isLeq(s2, st));

        Assertions.assertFalse(ord.isLeq(st, sb));
        Assertions.assertFalse(ord.isLeq(st, s1));
        Assertions.assertFalse(ord.isLeq(st, s2));
        Assertions.assertFalse(ord.isLeq(st, s3));
        Assertions.assertTrue(ord.isLeq(st, st));
    }
}
