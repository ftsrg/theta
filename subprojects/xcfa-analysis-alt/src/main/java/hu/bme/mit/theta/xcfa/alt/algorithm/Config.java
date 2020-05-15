package hu.bme.mit.theta.xcfa.alt.algorithm;

/**
 * A config might be inconsistent, always check when given to a
 */
public interface Config {
    boolean rememberTraces();
    boolean debug();
    boolean optimizeLocals();
    boolean discardAlreadyExplored();
    boolean isPartialOrder();

    class ImmutableConfig implements Config {
        private final boolean rememberTraces, debug, optimizeLocals, discardAlreadyExplored,
            partialOrder;

        private ImmutableConfig(boolean rememberTraces, boolean debug, boolean optimizeLocals, boolean discardAlreadyExplored, boolean partialOrder) {
            this.rememberTraces = rememberTraces;
            this.debug = debug;
            this.optimizeLocals = optimizeLocals;
            this.discardAlreadyExplored = discardAlreadyExplored;
            this.partialOrder = partialOrder;
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
    }

    public class Builder {
        public boolean rememberTraces = false;
        public boolean debug = false;
        /**
         * Optimize when there is a process with only local transitions,
         *  at least one of them being local.
         */
        public boolean optimizeLocals = false;

        public boolean discardAlreadyExplored = false;

        /**
         * Run with partial order reduction
         */
        public boolean partialOrder = false;

        public Config build() {
            return new ImmutableConfig(rememberTraces, debug, optimizeLocals, discardAlreadyExplored, partialOrder);
        }
    }
}
