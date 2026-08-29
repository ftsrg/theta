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

package hu.bme.mit.theta.xta.analysis.config;

import hu.bme.mit.theta.analysis.Cex;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.Proof;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;

public final class XtaConfig<Pr extends Proof, C extends Cex, P extends Prec> {

    private final SafetyChecker<Pr, C, P> checker;
    private final P initPrec;

    private XtaConfig(final SafetyChecker<Pr, C, P> checker, final P initPrec) {
        this.checker = checker;
        this.initPrec = initPrec;
    }

    public static <Pr extends Proof, C extends Cex, P extends Prec> XtaConfig<Pr, C, P> create(
            final SafetyChecker<Pr, C, P> checker, final P initPrec) {
        return new XtaConfig<>(checker, initPrec);
    }

    public SafetyResult<Pr, C> check() {
        return checker.check(initPrec);
    }
}
