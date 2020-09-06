/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.analysis.stateless;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.analysis.stateless.graph.ExecutionGraph;

import java.util.Map;

public final class StatelessMC {

    private final XCFA xcfa;

    private StatelessMC(XCFA xcfa) {
        this.xcfa = xcfa;
    }

    private boolean verify() {
        ExecutionGraph initialExecutionGraph = new ExecutionGraph();
        for(VarDecl<?> varDecl : xcfa.getGlobalVars()) {
            if(varDecl.getInitValue() != null) {
                initialExecutionGraph.addInitialWrite(varDecl, varDecl.getInitValue());
            }
        }

        State state = initialExecutionGraph.executeXcfa(xcfa);

        for (Map.Entry<XCFA.Process, XCFA.Process.Procedure.Location> entry : state.getCurrentLocs().entrySet()) {
            XCFA.Process.Procedure.Location location = entry.getValue();
            boolean deadlock = false;
            if (!location.isEndLoc()) {
                if(location.isErrorLoc()) {
                    System.out.println("Error location reached!");
                    return false;
                }
                deadlock = true;
            }
            if(deadlock) {
                System.out.println("Deadlock reached!");
                return false;
            }
        }

        return true;
    }

    public static boolean check(XCFA xcfa) {
        final StatelessMC statelessMC = new StatelessMC(xcfa);
        return statelessMC.verify();
    }
}
