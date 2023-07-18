/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis.expr;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils;

import java.util.Collection;

public final class XtaExprInvTransFunc implements InvTransFunc<BasicExprState, XtaAction, UnitPrec> {

    private final static XtaExprInvTransFunc INSTANCE = new XtaExprInvTransFunc();

    private XtaExprInvTransFunc() {
    }

    public static XtaExprInvTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends BasicExprState> getPreStates(BasicExprState state, XtaAction action, UnitPrec prec) {
        final Expr<BoolType> preExpr = XtaExplUtils.pre(state.toExpr(), action);
        return ImmutableList.of(BasicExprState.of(preExpr));
    }
}
