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
package hu.bme.mit.theta.sts.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.sts.STS;

/**
 * An LTS implementation for the STS formalism. The STS has only one enabled
 * Action for every State, namely the transition relation.
 */
public final class StsLts implements LTS<State, StsAction> {

	private final Collection<StsAction> actions;

	private StsLts(final STS sts) {
		checkNotNull(sts);
		this.actions = Collections.singleton(new StsAction(sts));
	}

	/**
	 * Creates a new LTS based on a STS.
	 *
	 * @param sts
	 * @return
	 */
	public static LTS<State, StsAction> create(final STS sts) {
		return new StsLts(sts);
	}

	@Override
	public Collection<StsAction> getEnabledActionsFor(final State state) {
		return actions;
	}

}
