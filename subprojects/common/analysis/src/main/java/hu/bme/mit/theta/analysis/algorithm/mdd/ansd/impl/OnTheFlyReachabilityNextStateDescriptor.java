/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import java.util.ArrayList;
import java.util.Objects;
import java.util.Optional;

public class OnTheFlyReachabilityNextStateDescriptor implements AbstractNextStateDescriptor {

    private final AbstractNextStateDescriptor wrapped;

    // This must be handle or to force traversing until the terminal level
    private final MddHandle target;

    private final KillSwitch killSwitch;

    private static class KillSwitch {
        private boolean killed = false;

        public boolean isKilled() {
            return killed;
        }

        public void setKilled(boolean killed) {
            this.killed = killed;
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        OnTheFlyReachabilityNextStateDescriptor that = (OnTheFlyReachabilityNextStateDescriptor) o;
        return Objects.equals(wrapped, that.wrapped);
    }

    @Override
    public int hashCode() {
        return wrapped.hashCode();
    }

    @Override
    public String toString() {
        return wrapped + "";
    }

    private OnTheFlyReachabilityNextStateDescriptor(
            AbstractNextStateDescriptor wrapped, MddHandle target, KillSwitch killSwitch) {
        this.wrapped = wrapped;
        this.target = Preconditions.checkNotNull(target);
        this.killSwitch = killSwitch;
        if (target.isTerminal() && !target.isTerminalZero()) {
            System.out.println("Stopping state space enumeration, violating state reached.");
//            killSwitch.setKilled(true);
        }
    }

    private static AbstractNextStateDescriptor of(
            AbstractNextStateDescriptor wrapped, MddHandle target, KillSwitch killSwitch) {
        return (wrapped == AbstractNextStateDescriptor.terminalEmpty())
                ? AbstractNextStateDescriptor.terminalEmpty()
                : new OnTheFlyReachabilityNextStateDescriptor(wrapped, target, killSwitch);
    }

    public static AbstractNextStateDescriptor of(
            AbstractNextStateDescriptor wrapped, MddHandle target) {
        return of(wrapped, target, new KillSwitch());
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        return killSwitch.isKilled()
                ? IntObjMapView.empty(EmptyNextStateDescriptor.INSTANCE)
                : new IntObjMapViews.Transforming<>(
                        wrapped.getDiagonal(localStateSpace),
                        (descriptor, key) -> {
                            if (key == null) return AbstractNextStateDescriptor.terminalEmpty();
                            return OnTheFlyReachabilityNextStateDescriptor.of(
                                    descriptor, target.get(key), killSwitch);
                        });
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {
        return killSwitch.isKilled()
                ? IntObjMapView.empty(IntObjMapView.empty(EmptyNextStateDescriptor.INSTANCE))
                : new IntObjMapViews.Transforming<>(
                        wrapped.getOffDiagonal(localStateSpace),
                        it ->
                                new IntObjMapViews.Transforming<>(
                                        it,
                                        (descriptor, key) -> {
                                            if (key == null)
                                                return AbstractNextStateDescriptor.terminalEmpty();
                                            return OnTheFlyReachabilityNextStateDescriptor.of(
                                                    descriptor, target.get(key), killSwitch);
                                        }));
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        return wrapped.split()
                .map(
                        iterable -> {
                            var list = new ArrayList<AbstractNextStateDescriptor>();
                            iterable.forEach(
                                    it ->
                                            list.add(
                                                    new OnTheFlyReachabilityNextStateDescriptor(
                                                            it, target, killSwitch)));
                            return list;
                        });
    }

    @Override
    public boolean evaluate() {
        return wrapped.evaluate();
    }
}
