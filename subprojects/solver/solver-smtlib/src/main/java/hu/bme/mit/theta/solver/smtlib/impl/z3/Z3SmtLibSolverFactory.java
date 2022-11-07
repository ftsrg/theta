package hu.bme.mit.theta.solver.smtlib.impl.z3;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverFactory;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager;

import java.nio.file.Path;

public class Z3SmtLibSolverFactory extends GenericSmtLibSolverFactory {
    public enum Z3ItpSupport {
        NONE, OLD, NEW
    }

    private final Z3ItpSupport itpSupport;

    private Z3SmtLibSolverFactory(Path solverPath, String[] args, Z3ItpSupport itpSupport) {
        super(solverPath, args);
        this.itpSupport = itpSupport;
    }

    public static Z3SmtLibSolverFactory create(Path solverPath, String[] args, Z3ItpSupport itpSupport) {
        return new Z3SmtLibSolverFactory(solverPath, args, itpSupport);
    }

    @Override
    public ItpSolver createItpSolver() {
        if(!itpSupport.equals(Z3ItpSupport.NONE)) {
            final var symbolTable = new GenericSmtLibSymbolTable();
            final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
            final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
            final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

            if(itpSupport.equals(Z3ItpSupport.OLD)) {
                return new Z3OldSmtLibItpSolver(symbolTable, transformationManager, termTransformer, solverBinary);
            }
            else if(itpSupport.equals(Z3ItpSupport.NEW)) {
                return new Z3NewSmtLibItpSolver(symbolTable, transformationManager, termTransformer, solverBinary);
            }
            else {
                throw new AssertionError();
            }
        }
        else {
            throw new UnsupportedOperationException("Z3 interpolation supported below 4.5.0 and above 4.8.8");
        }
    }
}
