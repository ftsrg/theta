package hu.bme.mit.theta.solver.smtlib.impl.mathsat;

import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibExprTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;

public class MathSATSmtLibExprTransformer extends GenericSmtLibExprTransformer {
    public MathSATSmtLibExprTransformer(final SmtLibTransformationManager transformer) {
        super(transformer);
    }

    @Override
    protected String transformIntRem(final IntRemExpr expr) {
        return String.format("(ite (< %2$s 0) (- (mod %1$s %2$s)) (mod %1$s %2$s))", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }
}
