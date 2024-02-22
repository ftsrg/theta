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
package hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl;

import hu.bme.mit.delta.collections.IntCursor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.DomainRegistry;

public class BoundedDomainRegistry implements DomainRegistry {
    private class BoundedDomainCursor implements IntCursor {
        private int current;

        public BoundedDomainCursor() {
            current = lowerBound - 1;
        }

        @Override
        public int elem() {
            assert current < lowerBound || current >= upperBound :
                    "This cursor does not point to an eleemnt fo the collection.";
            return current;
        }

        @Override
        public boolean moveNext() {
            if (current >= upperBound)
                return false;
            current++;
            return true;
        }

    }

    // Inclusive
    private int lowerBound = Integer.MAX_VALUE;
    // Exclusive
    private int upperBound = Integer.MIN_VALUE;

    @Override
    public void confirm(int value) {
        if (value < lowerBound) {
            lowerBound = value;
        }

        if (value > upperBound) {
            upperBound = value;
        }
    }

    @Override
    public void clear() {
        lowerBound = Integer.MAX_VALUE;
        upperBound = Integer.MIN_VALUE;
    }

    @Override
    public boolean contains(final int v) {
        return v <= upperBound && v >= lowerBound;
    }

    @Override
    public IntCursor cursor() {
        return new BoundedDomainCursor();
    }

    @Override
    public boolean isEmpty() {
        return lowerBound > upperBound;
    }

    @Override
    public boolean isProcedural() {
        return false;
    }

    @Override
    public int size() {
        return lowerBound > upperBound ? 0 : upperBound - lowerBound + 1;
    }

}
