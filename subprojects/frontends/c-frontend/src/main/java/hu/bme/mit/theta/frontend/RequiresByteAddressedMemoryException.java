/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.frontend;

/**
 * A construct that the cell-per-value memory models cannot express, but the byte-addressed one can.
 *
 * <p>The {@code multi} and {@code flat} models give each scalar one cell, so a union punned through
 * members of different widths has to be laid out as bytes by hand, and there the frontend runs out
 * of room: a pointer cannot say that it covers several cells ({@code &u.qwords[0]}), and a member
 * whose bytes must be recombined has no cell to be read from. Under {@code --memory-model bytes}
 * neither is a special case -- every object is a run of byte cells, a pointer is a plain byte
 * address, and a wider scalar is the concatenation of the cells it spans.
 *
 * <p>Raised instead of a plain {@link UnsupportedFrontendElementException} so the caller can tell
 * "this input needs byte granularity" apart from "this input is not supported at all", and retry
 * under the model that does support it rather than giving up on the task.
 *
 * <p><b>Not raised for a floating-point member.</b> The byte-addressed model refuses those too (see
 * {@code ByteMemoryPass}), because splitting a float means an IEEE bit reinterpretation that
 * SMT-LIB leaves underspecified for NaN. Retrying such an input would swap one refusal for another
 * and waste a whole second frontend build, so that case stays a plain unsupported-element failure.
 */
public class RequiresByteAddressedMemoryException extends UnsupportedFrontendElementException {
    public RequiresByteAddressedMemoryException(String message) {
        super(message);
    }
}
