package hu.bme.mit.theta.solver.smtlib.impl.mathsat;

import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibExprTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;

public class MathSATSmtLibTransformationManager extends GenericSmtLibTransformationManager {
    public MathSATSmtLibTransformationManager(final SmtLibSymbolTable symbolTable) {
        super(symbolTable);
    }

    @Override
    protected SmtLibExprTransformer instantiateExprTransformer(final SmtLibTransformationManager transformer) {
        return new MathSATSmtLibExprTransformer(transformer);
    }
}
