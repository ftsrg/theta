package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.ObjIntMap;
import com.koloboke.collect.map.hash.HashObjIntMaps;
import com.koloboke.collect.set.ObjSet;
import com.koloboke.collect.set.hash.HashObjSets;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.IntStatistics;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.common.container.Containers;

import java.util.Optional;
import java.util.Set;

/**
 * An MddSymbolicNode-based implementation of a {@link TraversalConstraint}.
 * For each variable, the lowest and highest values that appear on outgoing edges are collected.
 * If a variable appears in node with a default value or doesn't appear in the subtree at all, then no bounds are returned.
 */
public class MddSymbolicNodeTraversalConstraint implements TraversalConstraint{

    private final ObjIntMap<MddVariable> lowerBounds;
    private final ObjIntMap<MddVariable> upperBounds;
    private final ObjSet<MddVariable> hasDefaultValue;

    public MddSymbolicNodeTraversalConstraint(MddSymbolicNodeImpl rootNode){
        Preconditions.checkNotNull(rootNode);
        this.lowerBounds = HashObjIntMaps.newUpdatableMap();
        this.upperBounds = HashObjIntMaps.newUpdatableMap();
        this.hasDefaultValue = HashObjSets.newUpdatableSet();

        final Set<MddSymbolicNodeImpl> traversed = Containers.createSet();
        traverse(rootNode, traversed);
    }

    private void traverse(final MddSymbolicNodeImpl node,
                          final Set<MddSymbolicNodeImpl> traversed) {
        if (traversed.contains(node) || node.isTerminal()) {
            return;
        } else {
            traversed.add(node);
        }

        Preconditions.checkState(node.isComplete());
        final MddVariable variable = node.getSymbolicRepresentation().second;

        if(node.getCacheView().defaultValue() != null){
            final MddSymbolicNodeImpl defaultValue = (MddSymbolicNodeImpl) node.getCacheView().defaultValue();
            traverse(defaultValue, traversed);
            hasDefaultValue.add(variable);
        } else {
            final IntStatistics statistics = node.getCacheView().statistics();
            if(variable != null){
                lowerBounds.put(variable, Math.min(lowerBounds.getOrDefault(variable, Integer.MAX_VALUE), statistics.lowestValue()));
                upperBounds.put(variable, Math.max(upperBounds.getOrDefault(variable, Integer.MIN_VALUE), statistics.highestValue()));
            }

            for(var cur = node.getCacheView().cursor(); cur.moveNext();){
                if(cur.value() != null){
                    traverse((MddSymbolicNodeImpl) cur.value(), traversed);
                }
            }
        }



    }

    @Override
    public Optional<Pair<Integer, Integer>> getBoundsFor(MddVariable variable) {
        if(hasDefaultValue.contains(variable)) return Optional.empty();
        if(!lowerBounds.containsKey(variable) || !upperBounds.containsKey(variable)) return Optional.empty();
        return Optional.of(new Pair<>(lowerBounds.getInt(variable), upperBounds.getInt(variable)));
    }
}
