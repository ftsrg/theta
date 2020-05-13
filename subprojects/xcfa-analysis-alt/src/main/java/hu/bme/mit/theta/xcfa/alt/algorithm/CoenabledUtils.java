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
package hu.bme.mit.theta.xcfa.alt.algorithm;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.LockStmt;
import hu.bme.mit.theta.core.stmt.xcfa.UnlockStmt;
import hu.bme.mit.theta.xcfa.alt.expl.EdgeTransition;
import hu.bme.mit.theta.xcfa.alt.expl.ProcessTransitions;
import hu.bme.mit.theta.xcfa.alt.expl.StmtTransition;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;

/**
 * Dynamic partial ordering has a notion of co-enabledness, which tries to capture usage of locking.
 */
public class CoenabledUtils {

    private CoenabledUtils() { }

    /** returns whether there is a possibility
     * that the two transitions are co-enabled */
    public static boolean coenabled(ProcessTransitions p1, ProcessTransitions p2) {
        // TODO what exactly needs to be returned when the process contains two transitions?
        if (p1.transitionStream().count() == 1 && p2.transitionStream().count() == 1) {
            Transition a = p1.transitionStream().findAny().get();
            Transition b = p1.transitionStream().findAny().get();
            if (a instanceof EdgeTransition) {
                a = ((EdgeTransition) a).getInnerTransition();
            }
            if (b instanceof EdgeTransition) {
                b = ((EdgeTransition) b).getInnerTransition();
            }
            if (!(a instanceof StmtTransition)) {
                return true;
            }
            if (!(b instanceof StmtTransition)) {
                return true;
            }
            Stmt sa = ((StmtTransition) a).getStmt();
            Stmt sb = ((StmtTransition) b).getStmt();

            if (sa instanceof UnlockStmt && sb instanceof LockStmt) {
                if (((UnlockStmt) sa).getSyncVar() == ((LockStmt) sb).getSyncVar())
                    return false;
            }
            if (sa instanceof LockStmt && sb instanceof UnlockStmt) {
                if (((LockStmt) sa).getSyncVar() == ((UnlockStmt) sb).getSyncVar())
                    return false;
            }
        }
        // over-approximation
        return true;
    }
}
