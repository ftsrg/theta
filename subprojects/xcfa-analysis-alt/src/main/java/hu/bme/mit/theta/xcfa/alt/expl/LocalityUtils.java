/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/** Checks whether a transition is local or has effects among multiple threads.
 *  If a read or write occurs on a global variable, then it must be local.
 */
public final class LocalityUtils {

    private static final Set<VarDecl<? extends Type>> globals = new HashSet<>();

    /** TODO less hackish solution? */
    public static void init(XCFA xcfa) {
        globals.addAll(xcfa.getGlobalVars());
    }

    public static boolean isLocal(VarDecl<? extends Type> var) {
        return !globals.contains(var);
    }

    public static boolean isLocal(Transition transition) {
        return transition.isLocal();
    }

    public static boolean isLocal(Set<VarDecl<?>> vars) {
        return vars.stream().allMatch(LocalityUtils::isLocal);
    }

    /**
     * Find any process with all transitions local with at least one enabled transition, and pick one enabled
     * transition, if any
     * @param state state
     * @return an enabled transition, with all other transitions from the process being local
     */
    public static Optional<Collection<ExecutableTransition>> findAnyEnabledLocalTransition(ExplState state) {
        return TransitionUtils.getTransitionsMap(state) // find a process
                .map(inner->inner.collect(Collectors.toUnmodifiableSet()))
                .filter(inner->inner.stream().allMatch(LocalityUtils::isLocal)) // with all transitions local
                .map(   // filter enabled entries
                        processTransitions -> ExecutableTransitionUtils.streamExecutableTransitions(state, processTransitions.stream())
                ).map( // collect
                        processTransitions -> processTransitions.collect(Collectors.toUnmodifiableSet())
                ).filter( // we need to have at least one enabled transition
                        processTransitions -> !processTransitions.isEmpty()
                ).findAny() // any processTransition does it
                .map(x->x);
    }
}
