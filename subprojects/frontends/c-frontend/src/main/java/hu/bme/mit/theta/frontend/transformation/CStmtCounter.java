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

package hu.bme.mit.theta.frontend.transformation;

public class CStmtCounter {

    private int forLoops = 0;
    private int whileLoops = 0;
    private int branches = 0;

    public void incrementBranches() {
        branches++;
    }

    public void incrementForLoops() {
        forLoops++;
    }

    public void incrementWhileLoops() {
        whileLoops++;
    }

    public int getWhileLoops() {
        return whileLoops;
    }

    public int getForLoops() {
        return forLoops;
    }

    public int getBranches() {
        return branches;
    }
}
