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

package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.utils.XcfaLabelVarReplacer;

import java.util.*;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaSTTransFunc<S extends ExprState, A extends StmtAction, P extends Prec> implements TransFunc<XcfaState<S>, A, XcfaPrec<P>> {

	private final TransFunc<S, A, P> transFunc;

	private XcfaSTTransFunc(final TransFunc<S, A, P> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <S extends ExprState, A extends StmtAction, P extends Prec> XcfaSTTransFunc<S, A, P> create(final TransFunc<S, A, P> transFunc) {
		return new XcfaSTTransFunc<>(transFunc);
	}

	private P stateVarsIntoPrec(P globalPrec, XcfaSTState<S> state) {
		if (globalPrec instanceof ExplPrec) {
			ExplPrec explPrec = (ExplPrec) globalPrec;
			for (XcfaSTState<S>.ProcedureLocation procedureLocation : state.getCurrentStack()) {
				Set<VarDecl<?>> localVars = new HashSet<>();
				final Set<VarDecl<?>> precVars = explPrec.getVars();
				procedureLocation.getUsedVars().forEach((var, localVar) -> {
					if (precVars.contains(var))
						localVars.add(localVar);
				});
				if (!localVars.isEmpty())
					explPrec = explPrec.join(ExplPrec.of(localVars));
			}
			globalPrec = (P) explPrec;
		}
		return globalPrec;
	}

	@Override
	public Collection<? extends XcfaState<S>> getSuccStates(final XcfaState<S> inState, final A inAction, final XcfaPrec<P> prec) {
		XcfaSTState<S> state = (XcfaSTState<S>) inState;
		XcfaSTAction action = (XcfaSTAction) inAction;

		P globalPrec = stateVarsIntoPrec(prec.getGlobalPrec(), state);

		final Collection<XcfaSTState<S>> newStates = new ArrayList<>();
		for (final S succState : transFunc.getSuccStates(state.getGlobalState(), inAction, globalPrec)) {
			final XcfaSTState<S> newState = state.withState(succState).withLocation(action.getTarget());
			if (action.getLabels().size() > 0 && action.getLabels().get(0) instanceof XcfaLabel.ProcedureCallXcfaLabel) {
				XcfaLabel.ProcedureCallXcfaLabel callLabel = (XcfaLabel.ProcedureCallXcfaLabel) action.getLabels().get(0);
				Optional<XcfaProcedure> calledProcedure = state.getCurrentLoc().getParent().getParent().getProcedures()
						.stream().filter(procedure -> callLabel.getProcedure().equals(procedure.getName())).findAny();
				if (calledProcedure.isPresent()) {
					Map<VarDecl<?>, VarDecl<?>> reverseVarLut = state.getReverseVars();
					XcfaLabel.ProcedureCallXcfaLabel originalCallLabel = (XcfaLabel.ProcedureCallXcfaLabel) callLabel.accept(new XcfaLabelVarReplacer(), reverseVarLut);
					newState.push(calledProcedure.get().getParamInitLoc(originalCallLabel));
				}
			}
			if (newState.getCurrentLoc().isEndLoc() && newState.getCurrentLoc().getParent() != newState.getCurrentLoc().getParent().getParent().getMainProcedure()) {
				newState.pop();
			}
			newStates.add(newState);
		}
		return newStates;
	}
}
