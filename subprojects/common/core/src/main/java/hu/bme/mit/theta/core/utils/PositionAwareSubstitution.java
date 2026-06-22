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

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

import java.util.List;

public class PositionAwareSubstitution {
    private final List<Decl<?>> newDecls;
    private int i = 0;

    private PositionAwareSubstitution(final List<Decl<?>> newDecls) {
        this.newDecls = newDecls;
    }

    public static <T extends Type> Expr<T> substitute(final Expr<T> expr, final List<Decl<?>> newDecls) {
        return new PositionAwareSubstitution(newDecls).substitute(expr);
    }

    private <T extends Type> Expr<T> substitute(final Expr<T> expr) {
        if (expr instanceof final RefExpr<T> refExpr) {
            final Expr<T> result = TypeUtils.cast(newDecls.get(i), refExpr.getType()).getRef();
            i++;
            return result;
        }
        return expr.map(this::substitute);
    }
}
