package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Map;
import java.util.Objects;

/**
 * The triplet AbstractExplState-ExplState-ImmutableExplState is using the same idea as in
 * AbstractMap-HashMap-TreeMap: one "equals" method for two different implementations storing the same
 * data, without comparing the types themselves.
 */
public abstract class AbstractExplState {
    public abstract Valuation getValuation();
    // comparing two maps work
    public abstract Map<XCFA.Process, ImmutableProcessState> getLocations();

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || !(o instanceof AbstractExplState)) return false;
        AbstractExplState that = (AbstractExplState) o;
        // comparing two maps (with different implementations) work, see AbsractMap's equals method:
        // https://docs.oracle.com/javase/7/docs/api/java/util/AbstractMap.html
        return getValuation().equals(that.getValuation()) &&
                getLocations().equals(that.getLocations());
    }


    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append("ImmutableExplState{\nvaluation:\n");
        for (Decl<?> decl : getValuation().getDecls()) {
            s.append("  ").append(decl).append(" -> ").append(getValuation().eval(decl).get()).append("\n");
        }
        s.append("locations:\n");
        for (var x : getLocations().entrySet()) {
            s.append("  ").append(x.getKey()).append(" -> ").append(x.getValue()).append("\n");
        }
        s.append("}");
        return s.toString();
    }

    @Override
    public int hashCode() {
        return Objects.hash(getValuation(), getLocations());
    }

}
