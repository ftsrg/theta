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
package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.ArrayList;
import java.util.Collection;

public final class XstsInitFunc<S extends ExprState, P extends Prec> implements
        InitFunc<XstsState<S>, P> {

    private final InitFunc<S, ? super P> initFunc;

    private XstsInitFunc(final InitFunc<S, ? super P> initFunc) {
        this.initFunc = initFunc;
    }

    public static <S extends ExprState, P extends Prec> XstsInitFunc<S, P> create(
            final InitFunc<S, ? super P> initFunc) {
        return new XstsInitFunc<>(initFunc);
    }

    @Override
    public Collection<? extends XstsState<S>> getInitStates(final P prec) {
        final Collection<XstsState<S>> initStates = new ArrayList<>();
        for (final S subInitState : initFunc.getInitStates(prec)) {
            initStates.add(XstsState.of(subInitState, true, false));
        }
        return initStates;
    }
}
