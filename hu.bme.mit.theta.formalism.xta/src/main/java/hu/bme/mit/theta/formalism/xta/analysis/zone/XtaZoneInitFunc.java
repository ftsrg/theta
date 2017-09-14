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
package hu.bme.mit.theta.formalism.xta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class XtaZoneInitFunc implements InitFunc<ZoneState, ZonePrec> {

	private static final XtaZoneInitFunc INSTANCE = new XtaZoneInitFunc();

	private XtaZoneInitFunc() {
	}

	static XtaZoneInitFunc getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		return Collections.singleton(ZoneState.zero(prec.getVars()).transform().up().build());
	}

}
