/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.model;

import hu.bme.mit.delta.collections.IntSetView;

/**
 * Represents objects that keep track of the values of a domain that has already
 * been encountered during state space exploration. New values may be registered
 * through {@link DomainRegistry#confirm(int)}, an over-approximation of the
 * encountered values may be enumerated through
 * {@link DomainRegistry#enumerateValues()}.
 *
 * @author Vince
 */
public interface DomainRegistry extends IntSetView {
    /**
     * Registers {@code value} in the {@link DomainRegistry}. This {@code value}
     * will be guaranteed to be returned when traversing the stored values with
     * {@link DomainRegistry#enumerateValues()}.
     *
     * @param value The value to register.
     */
    public void confirm(int value);

    void clear();

    // /**
    //  * Returns a {@link IntCursor} that can be used to traversed the values
    //  * stored in this {@link DomainRegistry}. Implementors must guarantee that the
    //  * values previously passed to {@link DomainRegistry#confirm(int)} will be
    //  * returned by the cursor, but other values may also be returned
    //  * (over-approximation).
    //  *
    //  * @return A cursor to traverse the stored values.
    //  */
    // public IntCursor enumerateValues();
}
