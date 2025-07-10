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

import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.MddCanonizationStrategy;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;

public class IdentityTemplate implements MddNode.Template {

    private final MddNode continuation;

    public IdentityTemplate(MddNode continuation) {
        this.continuation = continuation;
    }

    @Override
    public RecursiveIntObjMapView<? extends MddNode> toCanonicalRepresentation(MddVariable mddVariable, MddCanonizationStrategy mddCanonizationStrategy) {
        return new IdentityRepresentation(continuation);
    }
}
