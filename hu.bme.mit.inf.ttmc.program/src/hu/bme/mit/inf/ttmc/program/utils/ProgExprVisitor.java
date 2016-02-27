package hu.bme.mit.inf.ttmc.program.utils;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.program.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.program.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;

public interface ProgExprVisitor<P, R> extends ExprVisitor<P, R> {

	public <ExprType extends Type> R visit(PrimedExpr<ExprType> expr, P param);
	public <DeclType extends Type> R visit(VarRefExpr<DeclType> expr, P param);
	public <ReturnType extends Type> R visit(ProcRefExpr<ReturnType> expr, P param);
	public <ReturnType extends Type> R visit(ProcCallExpr<ReturnType> expr, P param);

}
