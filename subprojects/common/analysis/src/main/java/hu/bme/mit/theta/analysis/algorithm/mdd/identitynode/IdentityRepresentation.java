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
package hu.bme.mit.theta.analysis.algorithm.mdd.identitynode;

import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.MddNode;
import java.util.Objects;

public class IdentityRepresentation implements RecursiveIntObjMapView<MddNode> {

    private final MddNode continuation;

    public IdentityRepresentation(MddNode continuation) {
        this.continuation = continuation;
    }

    public MddNode getContinuation() {
        return continuation;
    }

    @Override
    public boolean isEmpty() {
        return false;
    }

    @Override
    public boolean isProcedural() {
        return true;
    }

    @Override
    public boolean containsKey(int i) {
        return false;
    }

    @Override
    public MddNode get(int i) {
        return null;
    }

    @Override
    public MddNode defaultValue() {
        return null;
    }

    @Override
    public RecursiveIntObjCursor<? extends MddNode> cursor() {
        return null;
    }

    @Override
    public int size() {
        return 0;
    }

    @Override
    public boolean equals(Object that) {
        if (this == that) return true;
        if (that instanceof IdentityRepresentation identityRepresentation) {
            return Objects.equals(continuation, identityRepresentation.continuation);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return Objects.hash(continuation);
    }

    @Override
    public String toString() {
        return "--|--> " + continuation;
    }
}
