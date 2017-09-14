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

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.zone.ZoneDomain;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;

public final class XtaZoneAnalysis implements Analysis<ZoneState, XtaAction, ZonePrec> {

	private static final XtaZoneAnalysis INSTANCE = new XtaZoneAnalysis();

	private XtaZoneAnalysis() {
	}

	public static XtaZoneAnalysis getInstance() {
		return INSTANCE;
	}

	@Override
	public Domain<ZoneState> getDomain() {
		return ZoneDomain.getInstance();
	}

	@Override
	public InitFunc<ZoneState, ZonePrec> getInitFunc() {
		return XtaZoneInitFunc.getInstance();
	}

	@Override
	public TransferFunc<ZoneState, XtaAction, ZonePrec> getTransferFunc() {
		return XtaZoneTransferFunc.getInstance();
	}

}
