package hu.bme.mit.theta.xcfa.algorithmselection;

public class LoopCounter {
	LoopCounter instance = new LoopCounter();

	private static int forLoops = 0;
	private static int whileLoops = 0;

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
}
