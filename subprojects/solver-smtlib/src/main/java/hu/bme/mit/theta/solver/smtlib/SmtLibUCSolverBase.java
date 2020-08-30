package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.solver.UCSolver;

public abstract class SmtLibUCSolverBase implements UCSolver {
    protected final SmtLibSolverBinary solverBinary;
    protected final SmtLibSymbolTable symbolTable;
    protected final SmtLibTransformationManager transformationManager;
    protected final SmtLibTermTransformer termTransformer;

    public SmtLibUCSolverBase(final SmtLibSolverBinary solverBinary, final SmtLibSymbolTable symbolTable, final SmtLibTransformationManager transformationManager, final SmtLibTermTransformer termTransformer) {
        this.solverBinary = solverBinary;
        this.symbolTable = symbolTable;
        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;
    }
}
