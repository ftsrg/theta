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
package hu.bme.mit.theta.xta.analysis;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.xta.XtaProcess;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XtaInitAbstractor<SConcr extends State, SAbstr extends State> implements InitAbstractor<XtaState<SConcr>, XtaState<SAbstr>> {

    private final InitAbstractor<SConcr, SAbstr> initAbstractor;

    private XtaInitAbstractor(final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        this.initAbstractor = checkNotNull(initAbstractor);
    }

    public static <SConcr extends State, SAbstr extends State> XtaInitAbstractor<SConcr, SAbstr>
    create(final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        return new XtaInitAbstractor<>(initAbstractor);
    }

    @Override
    public XtaState<SAbstr> getInitAbstrState(final XtaState<SConcr> state) {
        final List<XtaProcess.Loc> locs = state.getLocs();
        final SConcr concrState = state.getState();
        final SAbstr abstrState = initAbstractor.getInitAbstrState(concrState);
        return XtaState.of(locs, abstrState);
    }
}
