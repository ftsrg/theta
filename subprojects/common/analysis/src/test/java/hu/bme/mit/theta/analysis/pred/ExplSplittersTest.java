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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.Collection;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class ExplSplittersTest {

    private final Expr<BoolType> x = Decls.Var("x", Bool()).getRef();
    private final Expr<BoolType> y = Decls.Var("y", Bool()).getRef();
    private final Expr<BoolType> z = Decls.Var("z", Bool()).getRef();
    private final Expr<BoolType> expr = And(Not(x), Or(Not(y), z));

    @Test
    public void testWhole() {
        final Collection<Expr<BoolType>> exprs = ExprSplitters.whole().apply(expr);
        Assertions.assertEquals(1, exprs.size());
        Assertions.assertEquals(expr, exprs.iterator().next());
    }

    @Test
    public void testConjuncts() {
        final Collection<Expr<BoolType>> exprs = ExprSplitters.conjuncts().apply(expr);
        Assertions.assertEquals(2, exprs.size());
        Assertions.assertTrue(exprs.contains(Not(x)));
        Assertions.assertTrue(exprs.contains(Or(Not(y), z)));
    }

    @Test
    public void testAtoms() {
        final Collection<Expr<BoolType>> exprs = ExprSplitters.atoms().apply(expr);
        Assertions.assertEquals(3, exprs.size());
        Assertions.assertTrue(exprs.contains(x));
        Assertions.assertTrue(exprs.contains(y));
        Assertions.assertTrue(exprs.contains(z));
    }
}
