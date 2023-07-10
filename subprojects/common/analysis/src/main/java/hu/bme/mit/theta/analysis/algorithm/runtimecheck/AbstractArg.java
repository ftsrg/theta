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

package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * An abstract ARG is a normal ARG combined with its precision. It is used to check is the analysis
 * makes any refinement progress or not by the {@link ArgCexCheckHandler}
 */
public class AbstractArg<S extends State, A extends Action, P extends Prec> {

    private final Collection<State> states;
    private final List<Optional<ArgEdge<S, A>>> inEdges;
    private final P prec;

    public AbstractArg(final ARG<S, A> arg, P prec) {
        inEdges = arg.getNodes().map(ArgNode::getInEdge).collect(Collectors.toList());
        states = arg.getNodes().map(ArgNode::getState).collect(Collectors.toList());
        this.prec = prec;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        AbstractArg<S, A, P> that = (AbstractArg<S, A, P>) o;
        // return (states.equals(that.states) && prec.equals(that.prec));
        return (states.equals(that.states) && prec.equals(that.prec) && inEdges.equals(
                that.inEdges));
    }

    @Override
    public int hashCode() {
        // return Objects.hash(states, prec);
        return Objects.hash(states, prec, inEdges);
    }

}

