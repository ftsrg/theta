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
import static java.util.Collections.emptyList;
import static java.util.Collections.emptySet;
import static java.util.stream.Collectors.toList;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.xta.Sync;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.IteratorDeclContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.SelectContext;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.TransitionContext;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

final class XtaTransition implements Scope {

    private final XtaProcessSymbol scope;
    private final SymbolTable symbolTable;

    private final String sourceState;
    private final String targetState;
    private final List<XtaIteratorSymbol> selections;
    private final Optional<XtaExpression> guard;
    private final Optional<XtaSync> sync;
    private final List<XtaUpdate> updates;

    public XtaTransition(final XtaProcessSymbol scope, final TransitionContext context) {
        checkNotNull(context);
        this.scope = checkNotNull(scope);
        symbolTable = new SymbolTable();

        sourceState = context.fSourceId.getText();
        targetState = context.fTargetId.getText();

        selections = new ArrayList<>();
        guard = extractGuard(context);
        sync = extractSync(context);
        updates = extractUpdates(context);

        declareAllSelections(context.fTransitionBody.fSelect);
    }

    private Optional<XtaSync> extractSync(final TransitionContext context) {
        return Optional.ofNullable(context.fTransitionBody.fSync).map(s -> new XtaSync(this, s));
    }

    private Optional<XtaExpression> extractGuard(final TransitionContext context) {
        return Optional.ofNullable(context.fTransitionBody.fGuard)
                .map(g -> new XtaExpression(this, g.fExpression));
    }

    private List<XtaUpdate> extractUpdates(final TransitionContext context) {
        if (context.fTransitionBody.fAssign != null) {
            if (context.fTransitionBody.fAssign.fExpressions != null) {
                return context.fTransitionBody.fAssign.fExpressions.stream()
                        .map(e -> new XtaUpdate(this, e))
                        .collect(toList());
            }
        }
        return emptyList();
    }

    private void declareAllSelections(final SelectContext context) {
        if (context != null) {
            if (context.fIteratorDecls != null) {
                context.fIteratorDecls.forEach(this::declare);
            }
        }
    }

    private void declare(final IteratorDeclContext context) {
        final XtaIteratorSymbol iteratorSymbol = new XtaIteratorSymbol(this, context);
        selections.add(iteratorSymbol);
        symbolTable.add(iteratorSymbol);
    }

    ////

    public void instantiate(final XtaProcess process, final Env env) {
        final XtaStateSymbol sourceSymbol = (XtaStateSymbol) resolve(sourceState).get();
        final XtaStateSymbol targetSymbol = (XtaStateSymbol) resolve(targetState).get();

        final Loc source = (Loc) env.eval(sourceSymbol);
        final Loc target = (Loc) env.eval(targetSymbol);

        final Collection<Expr<BoolType>> guards;
        if (guard.isPresent()) {
            final Expr<?> expr = guard.get().instantiate(env);
            final Expr<BoolType> guardExpr = TypeUtils.cast(expr, Bool());
            final Collection<Expr<BoolType>> conjuncts = ExprUtils.getConjuncts(guardExpr);
            guards = conjuncts.stream().map(e -> e).collect(toList());
        } else {
            guards = emptySet();
        }

        final List<Stmt> assignments =
                updates.stream().map(u -> u.instantiate(env)).collect(toList());
        final Optional<Sync> label = sync.map(s -> s.instantiate(env));

        process.createEdge(source, target, guards, label, assignments);
    }

    ////

    @Override
    public Optional<? extends Scope> enclosingScope() {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("TODO: auto-generated method stub");
    }

    @Override
    public Optional<Symbol> resolve(final String name) {
        final Optional<Symbol> symbol = symbolTable.get(name);
        if (symbol.isPresent()) {
            return symbol;
        } else {
            return scope.resolve(name);
        }
    }
}
