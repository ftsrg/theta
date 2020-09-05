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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Map;

public final class StatelessMC {

    private final XCFA xcfa;

    private StatelessMC(XCFA xcfa) {
        this.xcfa = xcfa;
    }

    private boolean verify() {
        State state = new State(xcfa);

        Tuple2<XCFA.Process, XCFA.Process.Procedure.Edge> edge;
        while( (edge = state.getOneStep()) != null) {
            if(edge.get2().getTarget().isErrorLoc()) {
                System.out.println("Error location reached!");
                return false;
            }
            for (Stmt stmt : edge.get2().getStmts()) {
                stmt.accept(new XcfaStmtExecutionVisitor(), Tuple3.of(state.getMutableValuation(), state, edge.get1()));
            }
            state.getCurrentLocs().put(edge.get1(), edge.get2().getTarget());
        }
        for (Map.Entry<XCFA.Process, XCFA.Process.Procedure.Location> entry : state.getCurrentLocs().entrySet()) {
            XCFA.Process process = entry.getKey();
            XCFA.Process.Procedure.Location location = entry.getValue();
            if (!location.isEndLoc()) {
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
