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
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Lt;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Xor;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.ToInt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.XorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

public class BoolTestUtils {

    private BoolTestUtils() {}

    public static Collection<?> BasicOperations() {
        final var p1 = Param("x", Int());
        final var p2 = Param("y", Int());
        final var p3 = Param("z", Int());
        final var p4 = Param("w", BvType.of(32));
        final var c1 = Const("c", Int());

        return Arrays.asList(
                new Object[][] {
                    {
                        IteExpr.class,
                        Ite(Geq(c1.getRef(), Int(0)), Int(1), Int(2)),
                        Ite(Lt(c1.getRef(), Int(0)), Int(2), Int(1))
                    },
                    {ImplyExpr.class, False(), Imply(True(), False())},
                    {ImplyExpr.class, False(), Imply(True(), False())},
                    {XorExpr.class, False(), Xor(True(), True())},
                    {OrExpr.class, True(), Or(True(), True())},
                    {ExistsExpr.class, True(), Exists(List.of(p1), Eq(p1.getRef(), Int(0)))},
                    {ForallExpr.class, False(), Forall(List.of(p1), Eq(p1.getRef(), Int(0)))},
                    {
                        ExistsExpr.class,
                        True(),
                        Exists(List.of(p1), Exists(List.of(p2), Eq(p1.getRef(), p2.getRef())))
                    },
                    {
                        ForallExpr.class,
                        False(),
                        Forall(List.of(p1), Forall(List.of(p2), Eq(p1.getRef(), p2.getRef())))
                    },
                    {
                        ExistsExpr.class,
                        False(),
                        Exists(
                                List.of(p1, p2),
                                Exists(
                                        List.of(p3),
                                        And(
                                                List.of(
                                                        Lt(p1.getRef(), p2.getRef()),
                                                        Lt(p2.getRef(), p3.getRef()),
                                                        Lt(p3.getRef(), p1.getRef())))))
                    },
                    {
                        ExistsExpr.class,
                        False(),
                        Exists(
                                List.of(p1, p4),
                                Exists(
                                        List.of(p3),
                                        And(
                                                List.of(
                                                        Lt(p1.getRef(), ToInt(p4.getRef())),
                                                        Lt(ToInt(p4.getRef()), p3.getRef()),
                                                        Lt(p3.getRef(), p1.getRef())))))
                    },
                });
    }
}
