package hu.bme.mit.theta.mcm.graph.classification;

public class Thread {
    private static int cnt = 0;
    private final int id = cnt++;

    private static final Thread initialThread = new Thread();
    public static Thread getInitialThread() {
        return initialThread;
    }

    @Override
    public String toString() {
        return "Thread_" + id;
    }
}
