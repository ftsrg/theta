/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
