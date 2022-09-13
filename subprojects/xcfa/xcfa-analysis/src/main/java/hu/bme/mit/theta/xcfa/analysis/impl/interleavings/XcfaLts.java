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

package hu.bme.mit.theta.xcfa.analysis.impl.interleavings;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public final class XcfaLts implements LTS<XcfaState<?>, XcfaAction> {
	@Override
	public Collection<XcfaAction> getEnabledActionsFor(final XcfaState<?> state) {
		final List<XcfaAction> xcfaActions = new ArrayList<>();
		for (Integer enabledProcess : state.getEnabledProcesses()) {
			final XcfaLocation loc = state.getProcessLocs().get(enabledProcess);
			for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
				final XcfaAction xcfaAction = XcfaAction.create(enabledProcess, outgoingEdge);
				xcfaActions.add(xcfaAction);
			}
			findSynchronizations(xcfaActions, state);
		}
		return xcfaActions;
	}

	private void findSynchronizations(List<XcfaAction> actions, XcfaState<?> state) {
		List<XcfaAction> noReceiveActions = new ArrayList<>();
		List<XcfaAction> receiveActions = new ArrayList<>();
		for (XcfaAction action : actions) {
			boolean receive = false;
			for (XcfaLabel label : action.getLabels()) {
				if(label instanceof XcfaLabel.FenceXcfaLabel && ((XcfaLabel.FenceXcfaLabel) label).getType().startsWith("receive")) {
					receiveActions.add(action);
					receive = true;
					break;
				}
			}
			if(!receive) noReceiveActions.add(action);
		}

		// TODO not send receive actions

		List<List<XcfaAction>> enabledSendActions = new ArrayList<>();
		for (XcfaAction action : noReceiveActions) {
			for (XcfaLabel sendLabel : action.getLabels()) {
				if(sendLabel instanceof XcfaLabel.FenceXcfaLabel && ((XcfaLabel.FenceXcfaLabel) sendLabel).getType().startsWith("send")) {
					List<XcfaAction> newAction = new ArrayList<>();
					newAction.add(action);
					String receiveString = "receive " + ((XcfaLabel.FenceXcfaLabel) sendLabel).getType().split(" ")[1];
					for(XcfaAction ra : receiveActions) {
						for (XcfaLabel label : ra.getLabels()) {
							if (label instanceof XcfaLabel.FenceXcfaLabel && ((XcfaLabel.FenceXcfaLabel) label).getType() == receiveString) {
								newAction.add(ra);
								break;
							}
						}
					}
					enabledSendActions.add(newAction); // TODO: repeat
					break;
				}
			}
		}

	}
}
