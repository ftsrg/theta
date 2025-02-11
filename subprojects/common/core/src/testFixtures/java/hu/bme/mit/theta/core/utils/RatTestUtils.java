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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.ToRat;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Add;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Div;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Eq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Geq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Gt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Leq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Lt;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Mul;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Neg;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Neq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Sub;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.ToInt;

import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.rattype.RatAddExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatEqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGtExpr;
import hu.bme.mit.theta.core.type.rattype.RatLeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatLtExpr;
import hu.bme.mit.theta.core.type.rattype.RatMulExpr;
import hu.bme.mit.theta.core.type.rattype.RatNegExpr;
import hu.bme.mit.theta.core.type.rattype.RatNeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;
import hu.bme.mit.theta.core.type.rattype.RatToIntExpr;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

public class RatTestUtils {

    private RatTestUtils() {}

    public static Collection<?> BasicOperations() {
        return Arrays.asList(
                new Object[][] {
                    {RatAddExpr.class, Rat(4, 1), Add(List.of(Rat(1, 1), Rat(3, 1)))},
                    {RatSubExpr.class, Rat(1, 1), Sub(Rat(4, 1), Rat(3, 1))},
                    {RatMulExpr.class, Rat(12, 1), Mul(List.of(Rat(4, 1), Rat(3, 1)))},
                    {RatDivExpr.class, Rat(4, 1), Div(Rat(12, 1), Rat(3, 1))},
                    {RatAddExpr.class, Rat(4, 1), Add(List.of(Rat(-1, 1), Rat(5, 1)))},
                    {RatSubExpr.class, Rat(-2, 1), Sub(Rat(4, 1), Rat(6, 1))},
                    {RatMulExpr.class, Rat(-12, 1), Mul(List.of(Rat(-4, 1), Rat(3, 1)))},
                    {RatDivExpr.class, Rat(-4, 1), Div(Rat(12, 1), Rat(-3, 1))},
                    {RatNegExpr.class, Rat(-13, 1), Neg(Rat(13, 1))},
                    {RatEqExpr.class, False(), Eq(Rat(1, 1), Rat(3, 1))},
                    {RatEqExpr.class, True(), Eq(Rat(3, 1), Rat(3, 1))},
                    {RatNeqExpr.class, True(), Neq(Rat(1, 1), Rat(3, 1))},
                    {RatNeqExpr.class, False(), Neq(Rat(3, 1), Rat(3, 1))},
                    {RatGeqExpr.class, False(), Geq(Rat(1, 1), Rat(3, 1))},
                    {RatGeqExpr.class, True(), Geq(Rat(3, 1), Rat(3, 1))},
                    {RatGtExpr.class, False(), Gt(Rat(1, 1), Rat(3, 1))},
                    {RatGtExpr.class, False(), Gt(Rat(3, 1), Rat(3, 1))},
                    {RatLeqExpr.class, True(), Leq(Rat(1, 1), Rat(3, 1))},
                    {RatLeqExpr.class, True(), Leq(Rat(3, 1), Rat(3, 1))},
                    {RatLtExpr.class, True(), Lt(Rat(1, 1), Rat(3, 1))},
                    {RatLtExpr.class, False(), Lt(Rat(3, 1), Rat(3, 1))},
                    {RatToIntExpr.class, Int(5), ToInt(Rat(11, 2))},
                    {IntToRatExpr.class, Rat(5, 1), ToRat(Int(5))},
                });
    }
}
