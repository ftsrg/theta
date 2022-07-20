/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis.impl.multithread;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.*;

public class XcfaProcessTransFunc<S extends ExprState, P extends Prec> implements TransFunc<XcfaProcessState<S>, XcfaProcessAction, P> {
    private final TransFunc<S, StmtAction, P> transFunc;

    public XcfaProcessTransFunc(final TransFunc<S, StmtAction, P> transFunc) {
        this.transFunc = transFunc;
    }


    @Override
    public Collection<? extends XcfaProcessState<S>> getSuccStates(final XcfaProcessState<S> state, final XcfaProcessAction action, final P prec) {
        final Collection<XcfaProcessState<S>> states = new ArrayList<>();
        Map<VarDecl<?>, Set<VarDecl<?>>> dependencies = new LinkedHashMap<>(state.getDependencies());
        for (XcfaLabel label : action.getEdge().getLabels()) {
            label.accept(new XcfaLabelDependencyCollector(), dependencies);
        }

        for (S succState : transFunc.getSuccStates(state.getState(), action, prec)) {
            states.add(new XcfaProcessState<>(succState, action.getEdge().getTarget(), dependencies));
        }
        return states;
    }

}
