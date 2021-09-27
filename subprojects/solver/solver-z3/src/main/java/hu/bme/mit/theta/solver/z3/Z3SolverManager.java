package hu.bme.mit.theta.solver.z3;

import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;

import static com.google.common.base.Preconditions.checkArgument;

public final class Z3SolverManager extends SolverManager {
    private static final Z3SolverManager INSTANCE = new Z3SolverManager();
    public static Z3SolverManager getInstance() {
        return INSTANCE;
    }

    private static final String NAME = "Z3";

    @Override
    public boolean managesSolver(final String name) {
        return NAME.equals(name);
    }

    @Override
    public SolverFactory getSolverFactory(final String name) {
        checkArgument(NAME.equals(name));
        return Z3SolverFactory.getInstance();
    }
}
