/*
 *  Copyright 2017 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xta.dsl.gen.XtaDslParser.InstantiationContext;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

final class XtaInstantiationSymbol implements Symbol {

    private final Scope scope;
    private final InstantiationContext context;

    public XtaInstantiationSymbol(final Scope scope, final InstantiationContext context) {
        this.scope = checkNotNull(scope);
        this.context = checkNotNull(context);
    }

    @Override
    public String getName() {
        return context.fId.getText();
    }

    public String getProcName() {
        return context.fProcId.getText();
    }

    public List<Expr<?>> getArgumentList(final Env env) {
        final List<Expr<?>> argumentList = context.fArgList.fExpressions.stream().map(e -> {
            final XtaExpression expression = new XtaExpression(scope, e);
            return expression.instantiate(env);
        }).collect(toList());
        return argumentList;
    }

}
