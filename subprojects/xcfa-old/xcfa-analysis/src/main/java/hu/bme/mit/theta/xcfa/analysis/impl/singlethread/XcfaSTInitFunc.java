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

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaSTInitFunc<S extends ExprState, P extends Prec> implements InitFunc<XcfaState<S>, XcfaPrec<P>> {
	private final XcfaLocation initLoc;
	private final InitFunc<S, ? super P> initFunc;

	private XcfaSTInitFunc(final XcfaLocation initLoc, final InitFunc<S, ? super P> initFunc) {
		this.initLoc = checkNotNull(initLoc);
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends ExprState, P extends Prec> XcfaSTInitFunc<S, P> create(final XcfaLocation initLoc, final InitFunc<S, ? super P> initFunc) {
		return new XcfaSTInitFunc<>(initLoc, initFunc);
	}

	@Override
	public Collection<XcfaSTState<S>> getInitStates(final XcfaPrec<P> prec) {
		final Collection<XcfaSTState<S>> set = new ArrayList<>();
		for (S s : initFunc.getInitStates(prec.getGlobalPrec())) {
			final XcfaSTState<S> xcfaState = XcfaSTState.create(initLoc, s);
			set.add(xcfaState);
		}
		return set;
	}
}
