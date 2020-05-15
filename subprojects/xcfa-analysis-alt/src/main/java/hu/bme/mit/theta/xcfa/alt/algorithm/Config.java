package hu.bme.mit.theta.xcfa.alt.algorithm;

/**
 * A config might be inconsistent, always check when given to a
 */
public interface Config {
    boolean rememberTraces();
    boolean debug();
    /**
     * Optimize when there is a process with only local transitions,
     *  at least one of them being local.
     */
    boolean optimizeLocals();
    boolean discardAlreadyExplored();
    /**
     * Reduce state graph with partial order reduction techniques
     */
    boolean isPartialOrder();

    /**
     * Force iterate every trace, do not exit, when an unsafe property is found
     */
    boolean forceIterate();

    class ImmutableConfig implements Config {
        private final boolean rememberTraces;
        private final boolean debug;
        private final boolean optimizeLocals;
        private final boolean discardAlreadyExplored;
        private final boolean partialOrder;
        private final boolean forceIterate;

        private ImmutableConfig(boolean rememberTraces, boolean debug, boolean optimizeLocals, boolean discardAlreadyExplored, boolean partialOrder, boolean forceIterate) {
            this.rememberTraces = rememberTraces;
            this.debug = debug;
            this.optimizeLocals = optimizeLocals;
            this.discardAlreadyExplored = discardAlreadyExplored;
            this.partialOrder = partialOrder;
            this.forceIterate = forceIterate;
        }

        @Override
        public boolean rememberTraces() {
            return rememberTraces;
        }

        @Override
        public boolean debug() {
            return debug;
        }

        @Override
        public boolean optimizeLocals() {
            return optimizeLocals;
        }

        @Override
        public boolean discardAlreadyExplored() {
            return discardAlreadyExplored;
        }

        @Override
        public boolean isPartialOrder() {
            return partialOrder;
        }

        @Override
        public boolean forceIterate() {
            return forceIterate;
        }
    }

    public class Builder {
        public boolean rememberTraces = false;
        public boolean debug = false;
        public boolean optimizeLocals = false;
        public boolean discardAlreadyExplored = false;
        public boolean partialOrder = false;
        public boolean forceIterate = false;

        public Config build() {
            return new ImmutableConfig(rememberTraces, debug, optimizeLocals, discardAlreadyExplored, partialOrder, forceIterate);
        }
    }
}
