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
package hu.bme.mit.theta.xcfa.alt.algorithm;

import hu.bme.mit.theta.xcfa.alt.expl.ProcessTransitions;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;

import java.util.Collection;

/**
 * Checks whether two transitions are dependent.
 * Two transitions are independent by definition, if
 * 1) One cannot disable the other
 * 2) Executing them in reverse order does not change the output
 *
 * Dependency can always be over-approximated.
 * We use the following fact:
 * Two transitions can only be dependent, if
 * 1) they are on the same process (hence can disable one another)
 * 2) one writes a variable the other accesses
 *
 * Note that two reads of the same variable are independent.
 *
 * Defining the dependency relation between two transition is easy:
 * If any depends on any transition, then they are dependent.
 * For two transition sets, any depends any -> dependent
 */
public class DependencyUtils {

    private static <T> boolean hasCommon(Collection<T> c1, Collection<T> c2) {
        return c1.stream().anyMatch(c2::contains);
    }

    public static boolean depends(Transition t1, Transition t2) {
        if (t1.getProcess() == t2.getProcess())
            return true;
        return hasCommon(t1.getRWVars(), t2.getWVars()) ||
                hasCommon(t2.getRWVars(), t1.getWVars());
    }

    public static boolean depends(ProcessTransitions pt, Transition tr) {
        return pt.transitionStream().anyMatch(t->depends(t, tr));
    }

    public static boolean depends(ProcessTransitions pt, ProcessTransitions tr) {
        return pt.transitionStream().anyMatch(t->depends(tr, t));
    }
}
