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

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransFunc;

public final class UnitAnalysis implements Analysis<UnitState, Action, UnitPrec> {

	private static final UnitAnalysis INSTANCE = new UnitAnalysis();

	private UnitAnalysis() {
	}

	public static UnitAnalysis getInstance() {
		return INSTANCE;
	}

	@Override
	public PartialOrd<UnitState> getPartialOrd() {
		return UnitOrd.getInstance();
	}

	@Override
	public InitFunc<UnitState, UnitPrec> getInitFunc() {
		return UnitInitFunc.getInstance();
	}

	@Override
	public TransFunc<UnitState, Action, UnitPrec> getTransFunc() {
		return UnitTransFunc.getInstance();
	}

}
