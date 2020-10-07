package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graphfilter.Filter;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

public abstract class Constraint {
    protected final Filter filter;
    protected final boolean not;

    public Constraint(Filter filter, boolean not) {
        this.filter = filter;
        this.not = not;
    }

    public abstract Result checkMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal);

    public abstract Result checkRm(MemoryAccess source, MemoryAccess target, String label);

    public static abstract class Result{}

    public static class AcyclicResult extends Result{}

    public static class CyclicResult extends AcyclicResult {
        private final Graph cycle;
        private final boolean isFinal;

        public CyclicResult(Graph cycle, boolean isFinal) {
            this.cycle = cycle;
            this.isFinal = isFinal;
        }

        public Graph getCycle() {
            return cycle;
        }

        public boolean isFinal() {
            return isFinal;
        }
    }

    public static class EmptyResult extends Result {}

    public static class NonEmptyResult extends EmptyResult {
        private final GraphOrNodeSet content;
        private final boolean isFinal;

        public NonEmptyResult(GraphOrNodeSet content, boolean isFinal) {
            this.content = content;
            this.isFinal = isFinal;
        }

        public boolean isFinal() {
            return isFinal;
        }

        public GraphOrNodeSet getContent() {
            return content;
        }
    }
}
