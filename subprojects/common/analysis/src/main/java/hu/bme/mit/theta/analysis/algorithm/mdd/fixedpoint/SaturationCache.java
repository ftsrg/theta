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
package hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint;

import hu.bme.mit.delta.java.mdd.BinaryOperationCache;
import hu.bme.mit.delta.java.mdd.Cache;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.TernaryOperationCache;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;

public final class SaturationCache implements Cache {
    private final BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode>
            saturateCache = new BinaryOperationCache<>();
    private final TernaryOperationCache<
                    MddNode, AbstractNextStateDescriptor, AbstractNextStateDescriptor, MddNode>
            relProdCache = new TernaryOperationCache<>();

    public BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode> getSaturateCache() {
        return saturateCache;
    }

    public TernaryOperationCache<
                    MddNode, AbstractNextStateDescriptor, AbstractNextStateDescriptor, MddNode>
            getRelProdCache() {
        return relProdCache;
    }

    @Override
    public void clear() {
        saturateCache.clear();
        relProdCache.clear();
    }

    @Override
    public long getCacheSize() {
        return saturateCache.getCacheSize() + relProdCache.getCacheSize();
    }

    @Override
    public long getQueryCount() {
        return saturateCache.getQueryCount() + relProdCache.getQueryCount();
    }

    @Override
    public long getHitCount() {
        return saturateCache.getHitCount() + relProdCache.getHitCount();
    }
}
