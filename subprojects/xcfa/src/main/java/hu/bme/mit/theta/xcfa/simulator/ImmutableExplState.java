package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Map;
import java.util.Objects;

/**
 * All the data needed for determining if two states are equal.
 * TODO Currently does not support nested functions properly.
 */
public class ImmutableExplState extends AbstractExplState {

    private final ImmutableValuation valuation;
    private final ImmutableMap<XCFA.Process, ImmutableProcessState> locs;

    public ImmutableExplState(ImmutableValuation valuation, ImmutableMap<XCFA.Process, ImmutableProcessState> locs) {
        this.valuation = valuation;
        this.locs = locs;
    }

    @Override
    public Valuation getValuation() {
        return valuation;
    }

    @Override
    public Map<XCFA.Process, ImmutableProcessState> getLocations() {
        return locs;
    }

    @Override
    public int hashCode() {
        return Objects.hash(valuation, locs);
    }
}
