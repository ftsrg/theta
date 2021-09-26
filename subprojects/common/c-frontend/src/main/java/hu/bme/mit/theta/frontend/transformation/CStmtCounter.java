package hu.bme.mit.theta.frontend.transformation;

import java.util.LinkedHashSet;

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
