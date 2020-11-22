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

import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph.ExecutionGraph;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Optional;

public final class StatelessMC {
    public static boolean check(XCFA xcfa, MCM mcm, File cex, XcfaStatelessSettings settings) throws IOException {
        Optional<ExecutionGraph> violator = ExecutionGraph.execute(xcfa, mcm, settings);
        if(violator.isPresent()) {
            if(cex != null) {
                violator.get().printGraph(new FileWriter(cex));
            }
            return false;
        }
        return true;
    }
}
