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

package hu.bme.mit.theta.llvm2xcfa.handlers.states;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.llvm2xcfa.ArithmeticType;
import hu.bme.mit.theta.llvm2xcfa.SSAProvider;
import hu.bme.mit.theta.xcfa.model.XcfaBuilder;
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static hu.bme.mit.theta.llvm2xcfa.Utils.createConstant;
import static hu.bme.mit.theta.llvm2xcfa.Utils.createVariable;

public class GlobalState {
    private final XcfaBuilder builder;
    private final Map<String, VarDecl<?>> globalVars;
    private final List<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> procedures;
    private final SSAProvider ssa;
    private final ArithmeticType arithmeticType;
    private int globalCounter = 0;

    public GlobalState(SSAProvider ssa, ArithmeticType arithmeticType) {
        this.ssa = ssa;
        this.arithmeticType = arithmeticType;
        builder = new XcfaBuilder("llvm");
        this.globalVars = new HashMap<>();
        this.procedures = new ArrayList<>();

        // Creating global variables
        for (Tuple3<String, String, String> globalVariable : ssa.getGlobalVariables()) {
            VarDecl<?> variable = createVariable(globalVariable.get1(), globalVariable.get2());
            globalVars.put(globalVariable.get1(), variable);
            builder.addVar(new XcfaGlobalVar(variable, createConstant(variable.getType(), globalVariable.get3())));
        }

        procedures.addAll(ssa.getFunctions());
    }

    public void finalizeGlobalState(BuiltState builtState) {
    }

    public Map<String, VarDecl<?>> getGlobalVars() {
        return globalVars;
    }

    public void addGlobalVar(String name, VarDecl<?> globalVar) {
        this.globalVars.put(name, globalVar);
    }

    public int getGlobalCounter() {
        int cnt = globalCounter;
        ++globalCounter;
        return cnt;
    }

    public List<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> getProcedures() {
        return procedures;
    }

    public void addProcedure(Tuple3<String, Optional<String>, List<Tuple2<String, String>>> proc) {
        procedures.add(proc);
    }

    public SSAProvider getProvider() {
        return ssa;
    }

    public XcfaBuilder getBuilder() {
        return builder;
    }

    public ArithmeticType getArithmeticType() {
        return arithmeticType;
    }
}
