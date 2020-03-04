package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Objects;

public class ImmutableProcessState {
    final XCFA.Process.Procedure.Location loc;
    public ImmutableProcessState(XCFA.Process.Procedure.Location loc) {
        this.loc = loc;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ImmutableProcessState that = (ImmutableProcessState) o;
        return Objects.equals(loc, that.loc);
    }

    @Override
    public int hashCode() {
        return Objects.hash(loc);
    }
}
