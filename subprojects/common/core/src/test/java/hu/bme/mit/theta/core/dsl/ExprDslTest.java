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

import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Div;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neg;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Rem;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Gt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import java.util.Arrays;
import java.util.Collection;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class ExprDslTest {

    @Parameter(value = 0)
    public String actual;

    @Parameter(value = 1)
    public Expr<Type> expected;

    @Parameter(value = 2)
    public Collection<Decl<?>> decls;

    @Parameters
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {
                        "true or false and not 1%2 > 2%3",
                        Or(True(), And(False(), Not(Gt(Rat(1, 2), Rat(2, 3))))),
                        null
                    },
                    {
                        "true or (false and not 1 < 2)",
                        Or(True(), And(False(), Not(Lt(Int(1), Int(2))))),
                        null
                    },
                    {
                        "(true or false) and not - 5 = 4 - 1",
                        And(Or(True(), False()), Not(Eq(Neg(Int(5)), Sub(Int(4), Int(1))))),
                        null
                    },
                    {"true iff false imply true", Iff(True(), Imply(False(), True())), null},
                    {
                        "1 * 2 * 3 /= 4 - 1",
                        Neq(Mul(Int(1), Int(2), Int(3)), Sub(Int(4), Int(1))),
                        null
                    },
                    {"(1 mod 2) <= 4 / 5", Leq(Mod(Int(1), Int(2)), Div(Int(4), Int(5))), null},
                    {
                        "if 1 >= 2 then 1 rem 2 else 3 mod 5",
                        Ite(Geq(Int(1), Int(2)), Rem(Int(1), Int(2)), Mod(Int(3), Int(5))),
                        null
                    },
                });
    }

    @Test
    public void test() {
        final CoreDslManager manager = new CoreDslManager();

        if (decls != null) {
            decls.forEach(decl -> manager.declare(decl));
        }

        Assert.assertEquals(expected, manager.parseExpr(actual));
    }
}
