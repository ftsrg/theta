/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.smtlib.impl.generic;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Test;

/** Response framing: how a raw solver byte stream is cut into individual responses. */
public final class ReadProcessorTest {

    /** Mirrors the framing loop in {@link GenericSmtLibSolverBinary.ProcessHandler}. */
    private static List<String> frame(final String stream) {
        final List<String> out = new ArrayList<>();
        GenericSmtLibSolverBinary.ReadProcessor rp = null;
        for (final char c : stream.toCharArray()) {
            if (rp == null) {
                rp = new GenericSmtLibSolverBinary.ReadProcessor();
            }
            rp.step(c);
            if (rp.isReady()) {
                out.add(rp.getResult().trim());
                rp = null;
            }
        }
        return out;
    }

    @Test
    public void framesLineResponses() {
        assertEquals(List.of("sat", "unsat", "success"), frame("sat\nunsat\nsuccess\n"));
    }

    @Test
    public void framesAParenthesisedResponseAfterALineResponse() {
        assertEquals(List.of("sat", "((x 1)\n  (y 2))"), frame("sat\n((x 1)\n  (y 2))\n"));
    }

    /**
     * Two parenthesised responses in a row. The first goes ready on its closing paren, leaving its
     * terminating newline unread; that newline must not put the reader into line mode, or the
     * second response is delivered one line at a time. {@code check-allsat} returns one such
     * response per model, so it fails loudly here and nowhere else.
     */
    @Test
    public void framesBackToBackParenthesisedResponses() {
        final String stream =
                "( (p false)\n"
                        + "  (q false) )\n"
                        + "( (p true)\n"
                        + "  (q true) )\n"
                        + "( (p true)\n"
                        + "  (q false) )\n"
                        + "sat\n";
        assertEquals(
                List.of(
                        "( (p false)\n  (q false) )",
                        "( (p true)\n  (q true) )",
                        "( (p true)\n  (q false) )",
                        "sat"),
                frame(stream));
    }

    @Test
    public void skipsBlankLinesBetweenResponses() {
        assertEquals(List.of("sat", "unsat"), frame("sat\n\n\n  \nunsat\n"));
    }

    @Test
    public void ignoresComments() {
        assertEquals(List.of("sat"), frame("; a comment\nsat\n"));
    }
}
