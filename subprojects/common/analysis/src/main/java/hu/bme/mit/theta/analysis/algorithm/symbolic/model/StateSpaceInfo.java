package hu.bme.mit.theta.analysis.algorithm.symbolic.model;

import hu.bme.mit.delta.collections.ElementChain;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.java.mdd.MddNode;

/**
 * Represents a sub-state space of the system under analysis. Instances of this
 * type have some sort of a decision diagram node underneath to represent the
 * reachable substates. This information may be accessed through
 * {@link StateSpaceInfo#hasInfiniteStates()}, which specifies if the
 * component has specific states or its state space is undefined (that is, it
 * can be in any state); {@link StateSpaceInfo#getLocalStateSpace()}, which
 * returns the local states (if any) associated with the underlying (top)
 * component (accessible through {@link StateSpaceInfo#getComponentChain()});
 * and {@link StateSpaceInfo#getLocalStateSpace(Component)} which extracts (a
 * possible over-approximation of) the same information for another component
 * lower in the ordered component chain.
 *
 * @author Vince
 */
public interface StateSpaceInfo {
    /**
     * Gets the trace info associated with the currently processed variable.
     *
     * @return The current trace info.
     */
    Object getTraceInfo();

    default <T> T getTraceInfo(Class<T> typeToken) {
        return typeToken.cast(getTraceInfo());
    }

    /**
     * Gets the underlying component chain, which refers to the top component of the
     * current subspace.
     *
     * @return The underlying {@link ElementChain} instance.
     */
    //public ElementChain<Object> getComponentChain();

    // TODO: this should be something like "hasNonEmptyDefaultContinuation" to suggest a non-empty default value in
    // the IntObjMapView

    /**
     * Returns true if the underlying component (accessible through
     * {@link #getComponentChain()}) is known to have specific reachable states,
     * false if its state space is undefined, that is, it can be in any state.
     *
     * @return True if the underlying component has specific reachable states, false
     * if its state space is undefined.
     */
    public boolean hasInfiniteStates();

    /**
     * Gets the local states of the underlying component that are contained in the
     * current sub-state space. <b>Returns {@code null} if
     * {@link #hasInfiniteStates()} returns false.</b>
     *
     * @return The local states of the underlying component that are contained in
     * the current sub-state space or {@code null} if the state space is
     * undefined.
     */
    public IntSetView getLocalStateSpace();

    // TODO: possible tweaking. When is it worth it to traverse the MDD and collect
    // the actual states instead of relying on the domain registry?

    /**
     * Gets the local states of {@code someLowerComponent} that are contained in the
     * current sub-state space. <b>Returns {@code null} if
     * the state space of {@code someLowerComponent} is undefined.</b>
     *
     * @return The local states of the underlying component that are contained in
     * the current sub-state space or {@code null} if the state space is
     * undefined.
     */
    public StateSpaceInfo getLocalStateSpace(Object someLowerComponent);

    public MddNode toStructuralRepresentation();
}
