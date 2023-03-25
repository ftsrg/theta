package hu.bme.mit.theta.analysis.algorithm;

import java.util.ArrayList;
import java.util.List;

public class PorLogger {
	public static List<Integer> exploredActions = new ArrayList<>();
	public static List<Long> exploredStates = new ArrayList<>();
	public static List<Long> preservedStates = new ArrayList<>();

	public static void exploreAction() {
		exploredActions.set(exploredActions.size() - 1, exploredActions.get(exploredActions.size() - 1) + 1);
	}
}
