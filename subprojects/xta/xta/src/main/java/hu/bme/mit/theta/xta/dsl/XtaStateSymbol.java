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
package hu.bme.mit.theta.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static java.util.stream.Collectors.toList;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.XtaProcess.LocKind;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.CommitContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.StateDeclContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.UrgentContext;
import java.util.Collection;
import java.util.Collections;

final class XtaStateSymbol implements Symbol {

    private final String name;
    private final LocKind kind;
    private final XtaExpression expression;

    public XtaStateSymbol(
            final XtaProcessSymbol scope,
            final StateDeclContext context,
            final UrgentContext urgent,
            final CommitContext commit) {
        checkNotNull(context);
        name = context.fId.getText();
        kind =
                isCommited(name, commit)
                        ? LocKind.COMMITTED
                        : isUrgent(name, urgent) ? LocKind.URGENT : LocKind.NORMAL;
        expression =
                context.fExpression != null ? new XtaExpression(scope, context.fExpression) : null;
    }

    private static boolean isUrgent(final String name, final UrgentContext urgent) {
        if (urgent == null) {
            return false;
        } else {
            return urgent.fStateList.fIds.stream().anyMatch(id -> id.getText().equals(name));
        }
    }

    private static boolean isCommited(final String name, final CommitContext commit) {
        if (commit == null) {
            return false;
        } else {
            return commit.fStateList.fIds.stream().anyMatch(id -> id.getText().equals(name));
        }
    }

    @Override
    public String getName() {
        return name;
    }

    public Loc instantiate(final XtaProcess process, final Env env) {
        final Collection<Expr<BoolType>> invars;
        if (expression == null) {
            invars = Collections.emptySet();
        } else {
            final Expr<?> expr = expression.instantiate(env);
            final Expr<BoolType> invar = TypeUtils.cast(expr, Bool());
            final Collection<Expr<BoolType>> conjuncts = ExprUtils.getConjuncts(invar);
            invars = conjuncts.stream().map(e -> e).collect(toList());
        }

        final Loc loc = process.createLoc(process.getName() + "_" + name, kind, invars);
        return loc;
    }
}
