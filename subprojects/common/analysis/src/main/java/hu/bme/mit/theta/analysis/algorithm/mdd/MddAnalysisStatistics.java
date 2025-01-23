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
package hu.bme.mit.theta.analysis.algorithm.mdd;

import hu.bme.mit.theta.analysis.algorithm.Statistics;

public class MddAnalysisStatistics extends Statistics {

    private final Long violatingSize;
    private final Long stateSpaceSize;
    private final Long hitCount;
    private final Long queryCount;
    private final Long cacheSize;

    public MddAnalysisStatistics(
            Long violatingSize,
            Long stateSpaceSize,
            Long hitCount,
            Long queryCount,
            Long cacheSize) {
        this.violatingSize = violatingSize;
        this.stateSpaceSize = stateSpaceSize;
        this.hitCount = hitCount;
        this.queryCount = queryCount;
        this.cacheSize = cacheSize;

        addStat("ViolatingSize", this::getViolatingSize);
        addStat("StateSpaceSize", this::getStateSpaceSize);
        addStat("HitCount", this::getHitCount);
        addStat("QueryCount", this::getQueryCount);
        addStat("CacheSize", this::getCacheSize);
    }

    public Long getViolatingSize() {
        return violatingSize;
    }

    public Long getStateSpaceSize() {
        return stateSpaceSize;
    }

    public Long getHitCount() {
        return hitCount;
    }

    public Long getQueryCount() {
        return queryCount;
    }

    public Long getCacheSize() {
        return cacheSize;
    }
}
