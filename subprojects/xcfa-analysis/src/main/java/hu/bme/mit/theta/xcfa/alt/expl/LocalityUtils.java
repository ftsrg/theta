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

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

/**
 * An optimization to shared memory checker algorithms is to determine if a state change is local.
 *
 * Local transition means that it does not access any global variables that might interfere with
 * the execution of the transition.
 * Any execution path is equivalent to one with the local transition executed first, if there is at least one.
 *
 * Note: If the execution path has some special property (not e.g. state reachability or deadlock checks),
 * then this might not be true.
 *
 * Note: To be more precise, if there is a local and a non-local transition in the same process,
 * then this will not hold. This is handled here, because XCFA does not enforce this property
 * (however a C code will not translate to this special case).
 * This also stands if the non-local transition is disabled(!)
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

    /** Returns whether every transition from the same process is local */
    private static boolean isLocal(ProcessTransitions processTransitions) {
        return processTransitions.transitionStream()
                .allMatch(LocalityUtils::isLocal);
    }
    /**
     * Find any process with all transitions local with at least one enabled transition, and pick one enabled
     * transition, if any.
     * This is for the core optimization of determining if a transition is local.
     * Look at the notes of {@link LocalityUtils} for notes on corner cases.
     * @return an enabled transition, with all other transitions from the process being local
     */
    public static Optional<ProcessTransitions> findAnyEnabledLocalProcessTransition(ExplState state) {
        return TransitionUtils.getProcessTransitions(state).stream()
                .filter(ProcessTransitions::hasAnyEnabledTransition)
                .filter(LocalityUtils::isLocal)
                .findAny();
    }

}
