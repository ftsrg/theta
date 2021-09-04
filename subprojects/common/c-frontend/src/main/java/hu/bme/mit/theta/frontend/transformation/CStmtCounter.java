package hu.bme.mit.theta.frontend.transformation;

public class CStmtCounter {
	CStmtCounter instance = new CStmtCounter();

	private static int forLoops = 0;
	private static int whileLoops = 0;
	private static int branches = 0;

	public static void incrementBranches() {
		branches++;
	}

	public static void incrementForLoops() {
		forLoops++;
	}

	public static void incrementWhileLoops() {
		whileLoops++;
	}

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
