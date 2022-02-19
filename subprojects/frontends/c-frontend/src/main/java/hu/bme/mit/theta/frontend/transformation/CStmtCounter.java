/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
	CStmtCounter instance = new CStmtCounter();

	private static int forLoops = 0;
	private static int whileLoops = 0;
	private static int branches = 0;
// TODO this isn't so simple :c
//	private static Set<VarRef> controlVariables = new LinkedHashSet<>(); // variables, that come up in conditions
//	private static Set<VarRef> rightSideVariables = new LinkedHashSet<>(); // variables, that come up on the right side of assignments

/*
	public static void addRightSideVariable(VarRef var) {
		controlVariables.add(var);
	}

	public static void addControlVariable(VarRef var) {
		controlVariables.add(var);
	}

 */

	public static void incrementBranches() {
		branches++;
	}

	public static void incrementForLoops() {
		forLoops++;
	}

	public static void incrementWhileLoops() {
		whileLoops++;
	}

	/*
	public static void getControlVariables() { return controlVariables.size(); }

	public static void getRightSideVariables() { return rightSideVariables.size(); }
	 */
	public static int getWhileLoops() {
		return whileLoops;
	}

	public static int getForLoops() {
		return forLoops;
	}

	public static int getBranches() {
		return branches;
	}
}
