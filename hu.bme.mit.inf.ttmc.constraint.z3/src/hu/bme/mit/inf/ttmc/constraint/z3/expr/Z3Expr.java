package hu.bme.mit.inf.ttmc.constraint.z3.expr;

import hu.bme.mit.inf.ttmc.constraint.solver.impl.WrapperExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface Z3Expr<ExprType extends Type> extends WrapperExpr<ExprType, com.microsoft.z3.Expr>{
}
