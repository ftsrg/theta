package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.HashMap;
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
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ImmutableExplState that = (ImmutableExplState) o;
        return valuation.equals(that.valuation) &&
                locs.equals(that.locs);
    }

    @Override
    public int hashCode() {
        return Objects.hash(valuation, locs);
    }

    public static class Builder {
        private final ImmutableValuation val;
        // TODO use immutablemap.Builder instead
        private final Map<XCFA.Process, ImmutableProcessState> locs;
        public Builder(ImmutableValuation val) {
            this.val = val;
            locs = new HashMap<>();
        }
        public void add(XCFA.Process proc, ImmutableProcessState location) {
            locs.put(proc, location);
        }
        public ImmutableExplState build() {
            return new ImmutableExplState(val, ImmutableMap.copyOf(locs));
        }
    }
}
