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
package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.BasicMultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.BasicStackableExprState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.MultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.StackableExprState;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

final class XcfaInitFunc<S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, P extends Prec> implements InitFunc<XcfaState<S, SS, SSS>, XcfaPrec<P>> {

	private final Map<Integer, XcfaLocation> initLocs;
	private final InitFunc<S, ? super P> initFunc;

	private XcfaInitFunc(final Map<Integer, XcfaLocation> initLocs, final InitFunc<S, ? super P> initFunc) {
		this.initLocs = Collections.unmodifiableMap(checkNotNull(initLocs));
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, P extends Prec> XcfaInitFunc<S, SS, SSS, P> create(final Map<Integer, XcfaLocation> initLocs,
																				  final InitFunc<S, ? super P> initFunc) {
		return new XcfaInitFunc<>(initLocs, initFunc);
	}

	@Override
	public Collection<XcfaState<S, SS, SSS>> getInitStates(final XcfaPrec<P> prec) {
		checkNotNull(prec);
		final Collection<XcfaState<S, SS, SSS>> initStates;
		final List<Tuple2<Integer, Collection<SS>>> listOfInitStates = new ArrayList<>();
		for (Map.Entry<Integer, XcfaLocation> entry : initLocs.entrySet()) {
			Integer key = entry.getKey();
			XcfaLocation initLoc = entry.getValue();
			final P subPrec = prec.getPrec(initLoc);
			final Collection<? extends S> subInitStates = initFunc.getInitStates(subPrec);
			Collection<SS> substates = new ArrayList<>();
			for (final S subInitState : subInitStates) {
				//noinspection unchecked
				final SS initState = (SS) BasicStackableExprState.of(List.of(XcfaLocationState.of(initLoc, subInitState)));
				substates.add(initState);
			}
			listOfInitStates.add(Tuple2.of(key, substates));
		}

		initStates = collectInitStates(listOfInitStates);

		return initStates;
	}

	private Collection<XcfaState<S, SS, SSS>> collectInitStates(List<Tuple2<Integer, Collection<SS>>> listOfInitStates) {
		return collectInitStates(0, listOfInitStates, new LinkedHashMap<>(), new ArrayList<>());
	}

	private Collection<XcfaState<S, SS, SSS>> collectInitStates(int idx, List<Tuple2<Integer, Collection<SS>>> listOfInitStates, Map<Integer, SS> current, Collection<XcfaState<S, SS, SSS>> ret) {
		if(idx < listOfInitStates.size()) {
			Tuple2<Integer, Collection<SS>> entry = listOfInitStates.get(idx);
			for (SS ss : entry.get2()) {
				current.put(entry.get1(), ss);
				collectInitStates(idx + 1, listOfInitStates, current, ret);
				current.remove(entry.get1());
			}
		} else {
			//noinspection unchecked
			ret.add(XcfaState.of((SSS) BasicMultiStackableExprState.of(current)));
		}
		return ret;
	}

}
