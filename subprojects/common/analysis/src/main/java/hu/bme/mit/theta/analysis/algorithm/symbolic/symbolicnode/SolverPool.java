package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.solver.Solver;

import java.util.LinkedList;
import java.util.function.Supplier;

public class SolverPool {

    private final static int STARTING_SIZE = 10;
    private final static int GROWING = 5;

    private final LinkedList<Solver> available;

    private final Supplier<Solver> solverSupplier;

    public SolverPool(Supplier<Solver> solverSupplier){
        this.solverSupplier = solverSupplier;
        this.available = new LinkedList<>();
        for(int i = 0; i< STARTING_SIZE; i++) this.available.add(solverSupplier.get());
    }

    public Solver requestSolver(){
        if(this.available.size() == 0) createNewSolvers();
        return this.available.removeFirst();
    }

    public void returnSolver(Solver solver){
        Preconditions.checkState(solver.getAssertions().isEmpty());
        this.available.add(solver);
    }

    private void createNewSolvers(){
        for (int i = 0; i < GROWING; i++) this.available.add(solverSupplier.get());
    }

}
