package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import static hu.bme.mit.theta.core.stmt.Stmts.Assume;

public class LimitVisitor extends CComplexType.CComplexTypeVisitor<Expr<?>, AssumeStmt> {
	public static final LimitVisitor instance = new LimitVisitor();

	@Override
	public AssumeStmt visit(CComplexType type, Expr<?> param) {
		return Assume(BoolLitExpr.of(true));
	}
}
