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

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.expl.ExplState;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;
import hu.bme.mit.theta.xcfa.alt.expl.TransitionUtils;
import hu.bme.mit.theta.xcfa.alt.transform.DefaultTransformation;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.runners.Parameterized.Parameter;
import static org.junit.runners.Parameterized.Parameters;

/**
 * Tests if for all finished (safe or unsafe) path (checked by ExplicitChecker),
 * there is a stuttering equivalent that is checked here.
 * Only tests the safe inputs. Its output probably only makes sense where
 */
@RunWith(Parameterized.class)
public class DynamicPOCheckerCompletenessTest {
    @Parameter()
    public String filepath;

    @Parameter(1)
    public Boolean shouldWork;

    @Parameters()
    public static Collection<Object[]> data() {
        // TODO create inverse filter
        // everything except big
        return FileListHelper.tests("atomic, mutex, function, loop, threads, safe, unsafe");
    }

    @Test
    public void test() throws IOException {
        System.out.println("Testing " + filepath);
        final InputStream inputStream = getClass().getResourceAsStream(filepath);

        var referenceConfig = XcfaChecker.getSimpleExplicit();
        referenceConfig.rememberTraces = true;
        referenceConfig.optimizeLocals = false;
        referenceConfig.discardAlreadyExplored = false;
        referenceConfig.forceIterate = true;

        var sutConfig = XcfaChecker.getSimpleDPOR();
        sutConfig.rememberTraces = true;
        sutConfig.forceIterate = true;

        XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
        var reference = XcfaChecker.createChecker(xcfa, referenceConfig.build());
        var sut = XcfaChecker.createChecker(xcfa, sutConfig.build());

        var ref = reference.getTraces();
        var result = sut.getTraces();

        for (var path : result) {
            boolean good = false;
            for (var candidate : ref) {
                var t1 = candidate.getActions();
                var t2 = path.getActions();
                if (t1.size() != t2.size())
                    continue;
                good = true;
                for (int i = 0; i < t1.size(); i++) { // good when every pair of transitions match
                    if (!TransitionUtils.equals(t1.get(i), t2.get(i))) {
                        good = false;
                    }
                }
                if (good) {
                    break;
                }
            }
            Assert.assertTrue("Largely unexpected: a path is is DPOR, but not in explicit state graph.", good);
        }

        // The real question.
        Assert.assertTrue(
                "DPOR lost a path! No stuttering equivalent for a path in the explicit state graph.",
                ref.stream().allMatch( // for all path in reference
                        path -> result.stream().anyMatch( // there is a DPOR path
                                sutPath -> equivalent(path, sutPath) // that are equivalent
                        )
                )
        );
    }

    /** Checks whether two paths are stuttering equivalent
     * Assumes that DependencyUtils is used for checking dependencies
     *   in partial order reduction!
     * (Checking dependency uses over-approximation)
      */
    private boolean equivalent(Trace<ExplState, Transition> trace1, Trace<ExplState, Transition> trace2) {
        List<Transition> goalPath = trace1.getActions();
        List<Transition> path = trace2.getActions();
        if (goalPath.size() != path.size()) {
            return false;
        }
        // try to order path as it was in goalPath
        // copy to prevent any nasty side effects within the trace
        path = new ArrayList<>(path);
        for (int goalIdx = 0; goalIdx < goalPath.size(); goalIdx++) {
            Transition t = goalPath.get(goalIdx);
            int idx;
            for (idx = goalIdx; idx < path.size(); idx++) {
                if (TransitionUtils.equals(t, path.get(idx))) {
                    break;
                }
            }
            if (idx == path.size()) // not found
                return false;
            Preconditions.checkState(goalIdx <= idx);
            // bubble path[idx] to path[goalIdx]
            for (int j = idx; j > goalIdx; j--) {
                // swap path[j] and path[j-1] if they are independent

                Transition t1 = path.get(j-1);
                Transition t2 = path.get(j);
                if (DependencyUtils.depends(t1, t2)) {
                    return false;
                }
                path.set(j, t1);
                path.set(j-1, t2);
            }
        }
        return true;
    }

}
