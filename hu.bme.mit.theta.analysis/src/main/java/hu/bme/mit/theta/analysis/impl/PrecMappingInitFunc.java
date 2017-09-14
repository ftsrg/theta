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

import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

final class PrecMappingInitFunc<S extends State, PP extends Prec, PR extends Prec> implements InitFunc<S, PP> {

	private final InitFunc<S, ? super PR> initFunc;
	private final Function<? super PP, ? extends PR> mapping;

	private PrecMappingInitFunc(final InitFunc<S, ? super PR> initFunc,
			final Function<? super PP, ? extends PR> mapping) {
		this.initFunc = checkNotNull(initFunc);
		this.mapping = checkNotNull(mapping);
	}

	public static <S extends State, PP extends Prec, PR extends Prec> PrecMappingInitFunc<S, PP, PR> create(
			final InitFunc<S, ? super PR> initFunc, final Function<? super PP, ? extends PR> mapping) {
		return new PrecMappingInitFunc<>(initFunc, mapping);
	}

	@Override
	public Collection<? extends S> getInitStates(final PP prec) {
		return initFunc.getInitStates(mapping.apply(prec));
	}

}
