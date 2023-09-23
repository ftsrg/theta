package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.ArrayList;
import java.util.List;

public class COILogger {
    static long coiTimer = 0;
    static long allTimer = 0;
    static long nopTimer = 0;
    static long originalTimer = 0;
    static long ltsTimer = 0;
    static long transFuncTimer = 0;
    private static long startCoi = 0;
    private static long startAll = 0;
    private static long startNop = 0;
    private static long startOriginal = 0;
    private static long startLts = 0;
    private static long startTransFunc = 0;
    public static void startCoiTimer() {
        startCoi = System.currentTimeMillis();
    }
    public static void stopCoiTimer() {
        coiTimer += System.currentTimeMillis() - startCoi;
    }
    public static void startAllTimer() {
        startAll = System.currentTimeMillis();
    }
    public static void stopAllTimer() {
        allTimer += System.currentTimeMillis() - startAll;
    }
    public static void startNopTimer() {
        startNop = System.currentTimeMillis();
    }
    public static void stopNopTimer() {
        nopTimer += System.currentTimeMillis() - startNop;
    }
    public static void startOriginalTimer() {
        startOriginal = System.currentTimeMillis();
    }
    public static void stopOriginalTimer() {
        originalTimer += System.currentTimeMillis() - startOriginal;
    }
    public static void startLtsTimer() {
        startLts = System.currentTimeMillis();
    }
    public static void stopLtsTimer() {
        ltsTimer += System.currentTimeMillis() - startLts;
    }
    public static void startTransFuncTimer() {
        startTransFunc = System.currentTimeMillis();
    }
    public static void stopTransFuncTimer() {
        transFuncTimer += System.currentTimeMillis() - startTransFunc;
    }

    static long nops = 0;
    static List<Long> nopsList = new ArrayList<>();
    static long allLabels = 0;
    static List<Long> allLabelsList = new ArrayList<>();
    public static void incNops() {
        nops++;
    }
    public static void incAllLabels() {
        allLabels++;
    }
    public static void newIteration() {
        nopsList.add(nops);
        allLabelsList.add(allLabels);
        nops = 0;
        allLabels = 0;
    }
}
