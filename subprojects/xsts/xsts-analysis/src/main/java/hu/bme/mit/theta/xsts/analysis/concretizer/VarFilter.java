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
package hu.bme.mit.theta.xsts.analysis.concretizer;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Optional;

public final class VarFilter {

    private final XSTS xsts;

    private VarFilter(final XSTS xsts) {
        this.xsts = xsts;
    }

    public static VarFilter of(final XSTS xsts) {
        return new VarFilter(xsts);
    }

    public Valuation filter(final Valuation valuation) {
        MutableValuation filteredValuation = new MutableValuation();
        for (VarDecl decl : xsts.getVars()) {
            Optional<LitExpr> val = valuation.eval(decl);
            if (val.isPresent()) {
                filteredValuation.put(decl, val.get());
            }
        }
        return filteredValuation;
    }

}
