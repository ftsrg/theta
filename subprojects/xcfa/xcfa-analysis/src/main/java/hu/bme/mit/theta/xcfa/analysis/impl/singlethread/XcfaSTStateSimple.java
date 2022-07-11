package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Objects;

public class XcfaSTStateSimple <S extends ExprState> extends XcfaSTState<S> {
    private final XcfaLocation currentLocation;

    protected XcfaSTStateSimple(final XcfaLocation currentLoc, final S globalState) {
        super(globalState);
        this.currentLocation = currentLoc;
    }

    @Override
    public XcfaLocation getCurrentLoc() {
        return currentLocation;
    }

    @Override
    public boolean equalLocations(XcfaSTState<?> o) {
        XcfaSTStateSimple<?> that = (XcfaSTStateSimple<?>) o;
        return this.currentLocation.equals(that.currentLocation);
    }

    @Override
    public int hashCode() {
        return Objects.hash(currentLocation, globalState);
    }

    @Override
    public XcfaSTState<S> withState(S succState) {
        return new XcfaSTStateSimple<>(this.currentLocation, succState);
    }

    @Override
    public XcfaSTState<S> withLocation(XcfaLocation location) {
        return new XcfaSTStateSimple<>(location, this.globalState);
    }
}
