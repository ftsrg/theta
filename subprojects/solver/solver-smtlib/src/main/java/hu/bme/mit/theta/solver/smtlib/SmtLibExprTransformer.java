package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.core.type.Expr;

public interface SmtLibExprTransformer {
    String toTerm(Expr<?> expr);
}
