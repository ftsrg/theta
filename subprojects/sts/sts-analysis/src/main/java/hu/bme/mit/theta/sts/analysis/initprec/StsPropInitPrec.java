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
package hu.bme.mit.theta.sts.analysis.initprec;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.sts.STS;

/**
 * An implementation for initial precision that returns initial precisions based
 * on the property.
 */
public class StsPropInitPrec implements StsInitPrec {

	@Override
	public ExplPrec createExpl(final STS sts) {
		return ExplPrec.of(ExprUtils.getVars(sts.getProp()));
	}

	@Override
	public PredPrec createPred(final STS sts) {
		return PredPrec.of(ExprUtils.getAtoms(sts.getProp()));
	}

}
