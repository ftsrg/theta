/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

import java.util.Collection;
import java.util.function.Function;

public interface LazyStrategy<SConcr extends State, SAbstr extends State, S extends State, A extends Action> {

    Function<S, ?> getProjection();

    InitAbstractor<SConcr, SAbstr> getInitAbstractor();

    PartialOrd<SAbstr> getPartialOrd();

    boolean inconsistentState(final SConcr state);

    boolean mightCover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer);

    void cover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer, final Collection<ArgNode<S, A>> uncoveredNodes);

    void disable(final ArgNode<S, A> node, final A action, final S succState, final Collection<ArgNode<S, A>> uncoveredNodes);
}
