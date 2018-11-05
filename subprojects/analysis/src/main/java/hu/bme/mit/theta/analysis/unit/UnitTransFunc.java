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
package hu.bme.mit.theta.analysis.unit;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransFunc;

final class UnitTransFunc implements TransFunc<UnitState, Action, UnitPrec> {

	private static final UnitTransFunc INSTANCE = new UnitTransFunc();
	private static final Collection<UnitState> RESULT = ImmutableList.of(UnitState.getInstance());

	private UnitTransFunc() {
	}

	public static UnitTransFunc getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<UnitState> getSuccStates(final UnitState state, final Action action, final UnitPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);
		return RESULT;
	}

}
