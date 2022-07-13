package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.MddVariable;

import java.util.Optional;

public interface TraversalConstraint {

    Optional<Pair<Integer, Integer>> getBoundsFor(MddVariable variable);

}
