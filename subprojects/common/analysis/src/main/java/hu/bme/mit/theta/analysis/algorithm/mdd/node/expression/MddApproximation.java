/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.common.exception.NotSolvableException;

/**
 * Per-run policy for a node that exceeds the explicit edge limit, published to the exploration
 * through {@link MddExpressionRepresentation#APPROXIMATION}.
 */
public final class MddApproximation {

    public static final int DEFAULT_EDGE_LIMIT = 1000;

    public enum Strategy {
        /** Give up ({@code NotSolvableException}). */
        NONE,
        /** Keep the edges found so far, dropping the rest. Preserves {@code unsafe}. */
        UNDER,
        /** Drop the constraint on the level entirely. Preserves {@code safe}. */
        OVER,
    }

    private final Strategy strategy;
    private final int edgeLimit;

    private boolean overApproximated;
    private boolean underApproximated;

    private MddApproximation(final Strategy strategy, final int edgeLimit) {
        this.strategy = Preconditions.checkNotNull(strategy);
        Preconditions.checkArgument(
                edgeLimit > 0, "Edge limit must be positive, got %s", edgeLimit);
        this.edgeLimit = edgeLimit;
    }

    public static MddApproximation exact() {
        return new MddApproximation(Strategy.NONE, DEFAULT_EDGE_LIMIT);
    }

    public static MddApproximation of(final Strategy strategy, final int edgeLimit) {
        return new MddApproximation(strategy, edgeLimit);
    }

    public Strategy getStrategy() {
        return strategy;
    }

    public int getEdgeLimit() {
        return edgeLimit;
    }

    /** The state space became a superset of the real one; the exact strategy gives up instead. */
    public void overApproximate() {
        if (strategy == Strategy.NONE) {
            throw new NotSolvableException();
        }
        overApproximated = true;
    }

    void reportUnderApproximated() {
        underApproximated = true;
    }

    public boolean isOverApproximated() {
        return overApproximated;
    }

    public boolean isUnderApproximated() {
        return underApproximated;
    }

    @Override
    public String toString() {
        return strategy + " with edge limit " + edgeLimit;
    }
}
