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

import org.junit.Assert;
import org.junit.Test;

import java.util.Stack;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

public class SafetyTest {
    @Test
    public void simpleTest() {
        assertTrue(Safety.safe().isSafe());
        assertFalse(Safety.safe().isFinished());

        assertFalse(Safety.unsafe("x").isSafe());
        assertTrue(Safety.unsafe("x").isFinished());

        assertTrue(Safety.finished().isSafe());
        assertTrue(Safety.finished().isFinished());
    }

    /** */
    private static ProcessState getProcessState(CallState top, boolean singleCall) {
        Stack<CallState> s = new Stack<>();
        if (!singleCall)
            s.add(mock(CallState.class));
        s.add(top);
        return new ProcessState(s);
    }

    @Test
    public void callStateErrorTest() {
        CallState top = mock(CallState.class);
        when(top.isError()).thenReturn(true);

        var proc = getProcessState(top, false);

        var result = SafetyUtils.getSafety(proc);

        verify(top).isError();
        Assert.assertFalse(result.isSafe());
    }

    @Test
    public void callStateNormalTest() {
        var top = mock(CallState.class);
        var proc = getProcessState(top, false);
        when(top.isError()).thenReturn(false);
        when(top.isFinal()).thenReturn(false);

        var result = SafetyUtils.getSafety(proc);

        verify(top).isError();
        assertTrue(result.isSafe());
        assertFalse(result.isFinished());
    }

    @Test
    public void callStateFinalTest() {
        var top = mock(CallState.class);
        var proc = getProcessState(top, false);
        when(top.isError()).thenReturn(false);
        when(top.isFinal()).thenReturn(true);

        var result = SafetyUtils.getSafety(proc);

        verify(top).isError();
        assertTrue(result.isSafe());
        assertFalse(result.isFinished());
    }

    @Test
    public void singleCallStateFinalTest() {
        var top = mock(CallState.class);
        var proc = getProcessState(top, true);
        when(top.isError()).thenReturn(false);
        when(top.isFinal()).thenReturn(true);

        var result = SafetyUtils.getSafety(proc);

        verify(top).isError();
        verify(top).isFinal();
        assertTrue(result.isSafe());
        assertTrue(result.isFinished());
    }
}
