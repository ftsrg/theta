package hu.bme.mit.theta.xcfa.analysis.stateless;

import java.io.File;

public class XcfaStatelessSettings {
    private final int threadPoolSize;
    private final File statesDir;
    private final boolean insitu;
    private final int maxdepth;
    private final Long timeS;

    public XcfaStatelessSettings(int threadPoolSize, File statesDir, boolean insitu, int maxdepth, Long timeS) {
        this.threadPoolSize = threadPoolSize;
        this.statesDir = statesDir;
        this.insitu = insitu;
        this.maxdepth = maxdepth;
        this.timeS = timeS;
    }

    public int getThreadPoolSize() {
        return threadPoolSize;
    }

    public File getStatesDir() {
        return statesDir;
    }

    public boolean isInsitu() {
        return insitu;
    }

    public int getMaxdepth() {
        return maxdepth;
    }

    public Long getTimeS() {
        return timeS;
    }
}
