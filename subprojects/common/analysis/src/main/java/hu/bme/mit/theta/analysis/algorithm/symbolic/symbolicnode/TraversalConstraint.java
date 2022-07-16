package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.MddVariable;

import java.util.Optional;

/**
 * A constraint that can be used to restrict traversal of a subtree.
 */
public interface TraversalConstraint {

    /**
     * Gets the bounds for a variable if applicable
     * @param variable the variable
     * @return the bounds for the variable
     */
    Optional<Pair<Integer, Integer>> getBoundsFor(MddVariable variable);

}
