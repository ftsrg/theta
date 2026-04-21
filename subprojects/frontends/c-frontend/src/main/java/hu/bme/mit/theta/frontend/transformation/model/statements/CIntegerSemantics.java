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
package hu.bme.mit.theta.frontend.transformation.model.statements;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Div;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Mod;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.ModExpr;

public final class CIntegerSemantics {

    private CIntegerSemantics() {}

    /** Conversion from C (/) semantics to solver (div) semantics for Int values. */
    public static Expr<?> createIntDiv(Expr<?> a, Expr<?> b) {
        DivExpr<?> aDivB = Div(a, b);
        return Ite(
                Geq(a, Int(0)),
                aDivB,
                Ite(
                        Neq(Mod(a, b), Int(0)),
                        Ite(Geq(b, Int(0)), Add(aDivB, Int(1)), Sub(aDivB, Int(1))),
                        aDivB));
    }

    /** Conversion from C (%) semantics to solver (mod) semantics for Int values. */
    public static Expr<?> createIntMod(Expr<?> a, Expr<?> b) {
        ModExpr<?> aModB = Mod(a, b);
        return Ite(
                Eq(aModB, Int(0)),
                aModB,
                Ite(Geq(a, Int(0)), aModB, Ite(Geq(b, Int(0)), Sub(aModB, b), Add(aModB, b))));
    }
}
