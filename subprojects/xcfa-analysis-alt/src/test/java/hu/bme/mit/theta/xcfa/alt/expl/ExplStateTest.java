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

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;

import static org.junit.Assert.assertEquals;

public class ExplStateTest {

    static XCFA xcfa;

    @Before
    public  void init() throws IOException {
        final InputStream inputStream = getClass().getResourceAsStream("/functions-global-local.xcfa");
        xcfa = XcfaDslManager.createXcfa(inputStream);
    }

    @Test
    public void testEquality() {
        assertEquals(ImmutableExplState.initialState(xcfa), ImmutableExplState.initialState(xcfa));
        //noinspection AssertEqualsBetweenInconvertibleTypes
        assertEquals(ImmutableExplState.initialState(xcfa), MutableExplState.initialState(xcfa));
    }

    @Test
    public void testBasicUsageImmutable() {
        ImmutableExplState state = ImmutableExplState.initialState(xcfa);
        while (!state.getSafety().isFinished()) {
            System.err.println(state);
            state = state.getEnabledTransitions().iterator().next().execute();
        }
        // should not get into infinite loop
    }

    @Test
    public void testBasicUsageMutable() {
        MutableExplState state = MutableExplState.initialState(xcfa);
        while (!state.getSafety().isFinished()) {
            System.err.println(state);
            state.getEnabledTransitions().iterator().next().execute();
        }
        // should not get into infinite loop
    }
}