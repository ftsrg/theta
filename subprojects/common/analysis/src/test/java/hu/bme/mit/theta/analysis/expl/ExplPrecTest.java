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
package hu.bme.mit.theta.analysis.expl;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.inttype.IntType;
import java.util.Collections;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class ExplPrecTest {

    private final VarDecl<IntType> x = Var("x", Int());
    private final VarDecl<IntType> y = Var("y", Int());

    @Test
    public void testInstances() {
        final ExplPrec p1 = ExplPrec.empty();
        final ExplPrec p2 = ExplPrec.empty();
        final ExplPrec p3 = ExplPrec.of(Collections.emptySet());
        final ExplPrec p4 = ExplPrec.of(Collections.singleton(x));

        Assertions.assertSame(p1, p2);
        Assertions.assertSame(p1, p3);
        Assertions.assertNotSame(p1, p4);
        Assertions.assertSame(p2, p3);
        Assertions.assertNotSame(p2, p4);
        Assertions.assertNotSame(p3, p4);
    }

    @Test
    public void testMapping() {
        final ExplPrec prec = ExplPrec.of(Collections.singleton(x));
        final ExplState s1 =
                prec.createState(
                        ImmutableValuation.builder().put(x, Int(1)).put(y, Int(2)).build());
        final ExplState s2 = prec.createState(ImmutableValuation.builder().put(y, Int(2)).build());

        Assertions.assertEquals(1, s1.getDecls().size());
        Assertions.assertEquals(Int(1), s1.eval(x).get());
        Assertions.assertEquals(0, s2.getDecls().size());
    }

    @Test
    public void testRefinement() {
        final ExplPrec px = ExplPrec.of(Collections.singleton(x));
        final ExplPrec py = ExplPrec.of(Collections.singleton(y));
        final ExplPrec pxy = ExplPrec.of(ImmutableSet.of(x, y));

        final ExplPrec r1 = px.join(px);
        final ExplPrec r2 = px.join(py);
        final ExplPrec r3 = px.join(pxy);

        Assertions.assertSame(r1, px);
        Assertions.assertNotSame(r2, px);
        Assertions.assertSame(r3, pxy);
    }

    @Test
    public void testEquals() {
        final ExplPrec p1 = ExplPrec.empty();
        final ExplPrec p2 = ExplPrec.empty();
        final ExplPrec p3 = ExplPrec.of(Collections.emptySet());
        final ExplPrec p4 = ExplPrec.of(Collections.singleton(x));
        final ExplPrec p5 = ExplPrec.of(Collections.singleton(x));
        final ExplPrec p6 = ExplPrec.of(ImmutableSet.of(x, y));
        final ExplPrec p7 = ExplPrec.of(ImmutableSet.of(x, y));

        Assertions.assertEquals(p1, p2);
        Assertions.assertEquals(p1, p3);
        Assertions.assertEquals(p2, p3);
        Assertions.assertEquals(p4, p5);
        Assertions.assertEquals(p6, p7);

        Assertions.assertNotEquals(p1, p4);
        Assertions.assertNotEquals(p5, p7);
    }
}
