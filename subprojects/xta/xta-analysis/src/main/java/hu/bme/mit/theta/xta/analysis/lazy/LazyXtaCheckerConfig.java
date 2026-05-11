/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyChecker;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaState;

public class LazyXtaCheckerConfig<SConcr extends State, SAbstr extends State, P extends Prec> {

    private final LazyChecker<SConcr, SAbstr, XtaState<SConcr>, XtaState<SAbstr>, XtaAction, P>
            lazyXtaChecker;
    private final P prec;
    private ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction> arg;

    public LazyXtaCheckerConfig(
            final LazyChecker<SConcr, SAbstr, XtaState<SConcr>, XtaState<SAbstr>, XtaAction, P>
                    lazyXtaChecker,
            final P prec) {
        this.lazyXtaChecker = lazyXtaChecker;
        this.prec = prec;
    }

    public SafetyResult<
                    ARG<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>,
                    Trace<LazyState<XtaState<SConcr>, XtaState<SAbstr>>, XtaAction>>
            check() {
        return lazyXtaChecker.check(prec);
    }
}
