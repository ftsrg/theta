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
package hu.bme.mit.theta.analysis.algorithm.lazy.expl;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.singleton;

public final class ExplTransFunc<A extends Action> implements TransFunc<ExplState, A, UnitPrec> {

    private final ExplActionPost<A> explActionPost;

    private ExplTransFunc(final ExplActionPost<A> explActionPost) {
        checkNotNull(explActionPost);
        this.explActionPost = explActionPost;
    }

    public static <A extends Action> ExplTransFunc<A> create(final ExplActionPost<A> explActionPost) {
        return new ExplTransFunc<>(explActionPost);
    }

    @Override
    public Collection<ExplState> getSuccStates(final ExplState state, final A action, final UnitPrec prec) {
        checkNotNull(state);
        checkNotNull(action);
        checkNotNull(prec);
        return singleton(explActionPost.post(state, action));
    }

}
