/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis.zone;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.analysis.XtaAction;

import java.util.Collection;

public final class XtaZoneInvTransFunc implements InvTransFunc<ZoneState, XtaAction, ZonePrec> {

    private final static XtaZoneInvTransFunc INSTANCE = new XtaZoneInvTransFunc();

    private XtaZoneInvTransFunc() {
    }

    public static XtaZoneInvTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends ZoneState> getPreStates(ZoneState state, XtaAction action, ZonePrec prec) {
        final ZoneState preState = XtaZoneUtils.pre(state, action, prec);
        return ImmutableList.of(preState);
    }
}
