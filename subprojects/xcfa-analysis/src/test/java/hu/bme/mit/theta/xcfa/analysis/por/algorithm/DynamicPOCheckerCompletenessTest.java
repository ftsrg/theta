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
package hu.bme.mit.theta.xcfa.analysis.por.algorithm;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.analysis.por.expl.ExplState;
import hu.bme.mit.theta.xcfa.analysis.por.expl.Transition;
import hu.bme.mit.theta.xcfa.analysis.por.expl.TransitionUtils;
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
 * TODO probably erroneous
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
        // TODO there can be an issue with trace equivalency checking
        //     I do not want non-deterministically failing test, and this might be one
        //     The problem is that a POR trace might not be minimal if unsafe
        return FileListHelper.tests("atomic, mutex, function, loop, threads, safe");
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

        var refResult = reference.check();
        var sutResult = sut.check();
        var ref = reference.getTraces();
        var result = sut.getTraces();

        System.out.println("Statistics on num execution paths:");
        System.out.println("Exhaustive: " + ref.size());
        System.out.println("Dynamic parital order reduction: " + result.size());

        // C0
        Assert.assertEquals(ref.isEmpty(), result.isEmpty());

        Assert.assertEquals("Expected safety result to match", refResult.isSafe(), sutResult.isSafe());

        // PORs set of execution paths is a subset of exhaustive search
        for (var path : result) {
            boolean match = false;
            for (var candidate : ref) {
                var t1 = candidate.getActions();
                var t2 = path.getActions();
                if (t1.size() != t2.size())
                    continue;
                match = true;
                for (int i = 0; i < t1.size(); i++) { // good when every pair of transitions match
                    if (!TransitionUtils.equals(t1.get(i), t2.get(i))) {
                        match = false;
                    }
                }
                if (match) {
                    break;
                }
            }
            Assert.assertTrue("Largely unexpected: a path is is DPOR, but not in explicit state graph.", match);
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

    /** Checks whether two paths are stuttering equivalent.
     * Assumes that DependencyUtils is used for checking dependencies
     *   in partial order reduction!
     * (Checking dependency uses over-approximation)
     * Unsafety creates bit of an issue (the stuttering equivalency holds, but one trace sizes can mismatch)
      */
    private boolean equivalent(Trace<ExplState, Transition> trace1, Trace<ExplState, Transition> trace2) {
        // The process of making two runs equivalent by swapping consecutive transitions: (a,b,... are transitions)
        // Reach a,b,c from c,b,a
        // get "a" to the good place
        // swap b,a: c,a,b
        // swap a,c: a,c,b
        // fix "b"
        // swap c,b: a,b,c

        // There can be a transition that is not part of the other trace.
        // This should only be allowed if the trace is unsafe, because we never go further after getting an error.
        // TODO Currently the safety of the run is not checked, so this can return false positive.
        // Reach a,b,c (goal) from b,d,a,c
        // fix "a"
        // swap d,a: b,a,d,c
        // swap b,a: a,b,d,c
        // fix "b"
        // fix "c"
        // swap d,c: a,b,c,d
        // Note that "d" is never checked against anything

        // We also assume that one trace must be a subsequence of the other

        List<Transition> goalPath = trace1.getActions();
        List<Transition> path = trace2.getActions();
        // try to order path as it was in goalPath
        Assert.assertEquals(path.size(), goalPath.size()); // TODO remove if issue around unsafety is solved
        // path can bubble beyond last element (only when an error was reached)
        if (path.size() < goalPath.size()) {
            var s = path;
            path = goalPath;
            goalPath = s;
        }
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
            if (idx == path.size()) { // one trace must be the subsequence of the other
                return false;
            }
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
