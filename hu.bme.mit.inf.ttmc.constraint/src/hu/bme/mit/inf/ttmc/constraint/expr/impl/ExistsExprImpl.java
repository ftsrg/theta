package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class ExistsExprImpl extends AbstractQuantifiedExpr implements ExistsExpr {

	private static final String OPERATOR = "Exists";

	public ExistsExprImpl(Collection<? extends ParamDecl<? extends Type>> paramDecls,
			Expr<? extends BoolType> op) {
		super(paramDecls, op);
	}
	
	@Override
	public ExistsExpr withOp(Expr<? extends BoolType> op) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	protected String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected int getHashSeed() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}
	
	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
