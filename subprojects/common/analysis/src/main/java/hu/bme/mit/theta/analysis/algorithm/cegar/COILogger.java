package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.ArrayList;
import java.util.List;

public class COILogger {
    static long coiTimer = 0;
    static long transFuncTimer = 0;
    private static long startCoi = 0;
    private static long startTransFunc = 0;
    public static void startCoiTimer() {
        startCoi = System.currentTimeMillis();
    }
    public static void stopCoiTimer() {
        coiTimer += System.currentTimeMillis() - startCoi;
    }
    public static void startTransFuncTimer() {
        startTransFunc = System.currentTimeMillis();
    }
    public static void stopTransFuncTimer() {
        transFuncTimer += System.currentTimeMillis() - startTransFunc;
    }

    static long nops = 0;
    static List<Long> nopsList = new ArrayList<>();
    public static void incNops() {
        nops++;
    }
    public static void decNops() {
        nops--;
    }
    static long havocs = 0;
    static List<Long> havocsList = new ArrayList<>();
    public static void incHavocs() {
        havocs++;
    }
    public static void decHavocs() {
        havocs--;
    }
    static long allLabels = 0;
    static List<Long> allLabelsList = new ArrayList<>();
    public static void incAllLabels() {
        allLabels++;
    }
    static long exploredActions = 0;
    static List<Long> exploredActionsList = new ArrayList<>();
    public static void incExploredActions() {
        exploredActions++;
    }
    static long covers = 0;
    static List<Long> coversList = new ArrayList<>();
    public static void incCovers() {
        covers++;
    }
    public static void newIteration() {
        nopsList.add(nops);
        havocsList.add(havocs);
        allLabelsList.add(allLabels);
        exploredActionsList.add(exploredActions);
        coversList.add(covers);
        nops = 0;
        havocs = 0;
        allLabels = 0;
        exploredActions = 0;
        covers = 0;
    }
}
