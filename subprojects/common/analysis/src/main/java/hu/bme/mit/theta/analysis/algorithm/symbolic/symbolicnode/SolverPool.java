package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;

import java.util.LinkedList;
import java.util.function.Supplier;

public class SolverPool {

    private final static int STARTING_SIZE = 10;
    private final static int GROWING = 5;

    private int created = 0;

    private final LinkedList<Solver> available;

    private final SolverFactory solverFactory;

    public SolverPool(SolverFactory solverFactory) {
        this.solverFactory = solverFactory;
        this.available = new LinkedList<>();
        for (int i = 0; i < STARTING_SIZE; i++) this.available.add(solverFactory.createSolver());
    }

    public Solver requestSolver() {
        if (this.available.size() == 0) createNewSolvers();
        return this.available.removeFirst();
    }

    public void returnSolver(Solver solver) {
        Preconditions.checkState(solver.getAssertions().isEmpty(), "Only empty solvers can be returned");
        this.available.add(solver);
    }

    private void createNewSolvers() {
        for (int i = 0; i < GROWING; i++) this.available.add(solverFactory.createSolver());
        this.created = created + GROWING;
    }

    public int size() {
        return this.created;
    }

}
