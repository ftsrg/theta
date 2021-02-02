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
package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Function;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;

public final class PrecMappingAnalysis<S extends State, A extends Action, PP extends Prec, PR extends Prec>
		implements Analysis<S, A, PP> {

	private final PartialOrd<S> partialOrd;
	private final InitFunc<S, PP> initFunc;
	private final TransFunc<S, A, PP> transFunc;

	private PrecMappingAnalysis(final Analysis<S, ? super A, ? super PR> analysis,
								final Function<? super PP, ? extends PR> mapping) {
		checkNotNull(analysis);
		checkNotNull(mapping);
		this.partialOrd = analysis.getPartialOrd();
		this.initFunc = PrecMappingInitFunc.create(analysis.getInitFunc(), mapping);
		this.transFunc = PrecMappingTransFunc.create(analysis.getTransFunc(), mapping);
	}

	public static <S extends State, A extends Action, PP extends Prec, PR extends Prec> PrecMappingAnalysis<S, A, PP, PR> create(
			final Analysis<S, ? super A, ? super PR> analysis, final Function<? super PP, ? extends PR> mapping) {
		return new PrecMappingAnalysis<>(analysis, mapping);
	}

	@Override
	public PartialOrd<S> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<S, PP> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<S, A, PP> getTransFunc() {
		return transFunc;
	}

}
