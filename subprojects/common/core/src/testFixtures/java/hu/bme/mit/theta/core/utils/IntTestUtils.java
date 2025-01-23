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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Div;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neg;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Pos;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Rem;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;

import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGtExpr;
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLtExpr;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntPosExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

public class IntTestUtils {

    private IntTestUtils() {}

    public static Collection<?> BasicOperations() {
        final var c1 = Const("x", Int());

        return Arrays.asList(
                new Object[][] {
                    {IntAddExpr.class, Int(4), Add(List.of(Int(1), Int(3)))},
                    {IntSubExpr.class, Int(1), Sub(Int(4), Int(3))},
                    {IntMulExpr.class, Int(12), Mul(List.of(Int(4), Int(3)))},
                    {IntDivExpr.class, Int(4), Div(Int(12), Int(3))},
                    {IntModExpr.class, Int(1), Mod(Int(13), Int(3))},
                    {IntRemExpr.class, Int(1), Rem(Int(13), Int(3))},
                    {IntAddExpr.class, Int(4), Add(List.of(Int(-1), Int(5)))},
                    {IntSubExpr.class, Int(-2), Sub(Int(4), Int(6))},
                    {IntMulExpr.class, Int(-12), Mul(List.of(Int(-4), Int(3)))},
                    {IntDivExpr.class, Int(-4), Div(Int(12), Int(-3))},
                    {IntModExpr.class, Int(2), Mod(Int(-13), Int(3))},
                    {IntRemExpr.class, Int(1), Rem(Int(13), Int(3))},
                    {IntRemExpr.class, Int(-1), Rem(Int(13), Int(-3))},
                    {IntRemExpr.class, Int(2), Rem(Int(-13), Int(3))},
                    {IntRemExpr.class, Int(-2), Rem(Int(-13), Int(-3))},
                    {IntNegExpr.class, Int(-13), Neg(Int(13))},
                    {IntEqExpr.class, False(), Eq(Int(1), Int(3))},
                    {IntEqExpr.class, True(), Eq(Int(3), Int(3))},
                    {IntNeqExpr.class, True(), Neq(Int(1), Int(3))},
                    {IntNeqExpr.class, False(), Neq(Int(3), Int(3))},
                    {IntGeqExpr.class, False(), Geq(Int(1), Int(3))},
                    {IntGeqExpr.class, True(), Geq(Int(3), Int(3))},
                    {IntGtExpr.class, False(), Gt(Int(1), Int(3))},
                    {IntGtExpr.class, False(), Gt(Int(3), Int(3))},
                    {IntLeqExpr.class, True(), Leq(Int(1), Int(3))},
                    {IntLeqExpr.class, True(), Leq(Int(3), Int(3))},
                    {IntLtExpr.class, True(), Lt(Int(1), Int(3))},
                    {IntLtExpr.class, False(), Lt(Int(3), Int(3))},
                    {IntPosExpr.class, c1.getRef(), Pos(c1.getRef())},
                });
    }
}
