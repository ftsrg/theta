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

package hu.bme.mit.theta.xcfa.passes.xcfapass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.Map;
import java.util.Optional;

public class DemoteThreadLocalGlobals extends XcfaPass {

    @Override
    public XCFA.Builder run(XCFA.Builder builder) {
        for (Map.Entry<VarDecl<?>, Optional<LitExpr<?>>> entry : new ArrayList<>(
                builder.getGlobalVars().entrySet())) {
            VarDecl<?> varDecl = entry.getKey();
            Optional<LitExpr<?>> litExpr = entry.getValue();

            if (CComplexType.getType(varDecl.getRef()).isThreadLocal()) {
                builder.getGlobalVars().remove(varDecl);
                for (XcfaProcess.Builder process : builder.getProcesses()) {
                    process.createVar(varDecl, litExpr.orElse(null));
                }
            }
        }
        return builder;
    }
}
