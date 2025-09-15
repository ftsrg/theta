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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.Dereference;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import java.util.Collection;

final class ExprAtomCollector {

    private static final Collection<Class<?>> CONNECTIVES =
            ImmutableSet.<Class<?>>builder()
                    .add(NotExpr.class)
                    .add(ImplyExpr.class)
                    .add(IffExpr.class)
                    .add(AndExpr.class)
                    .add(OrExpr.class)

                    // .add(IteExpr.class)
                    .add(Dereference.class)
                    .add(PrimeExpr.class)
                    .build();

    private ExprAtomCollector() {}

    static void collectAtoms(
            final Expr<BoolType> expr, final Collection<Expr<BoolType>> collectTo) {
        if (CONNECTIVES.contains(expr.getClass())) {
            expr.getOps().stream()
                    .forEach(op -> collectAtoms(TypeUtils.cast(op, Bool()), collectTo));
        } else {
            collectTo.add(expr);
        }
    }
}
