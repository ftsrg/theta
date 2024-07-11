package hu.bme.mit.theta.analysis.algorithm.mdd;

import hu.bme.mit.theta.analysis.algorithm.Statistics;

public class MddAnalysisStatistics extends Statistics {

    private final Long violatingSize;
    private final Long stateSpaceSize;
    private final Long hitCount;
    private final Long queryCount;
    private final Long cacheSize;


    public MddAnalysisStatistics(Long violatingSize, Long stateSpaceSize, Long hitCount, Long queryCount, Long cacheSize) {
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
