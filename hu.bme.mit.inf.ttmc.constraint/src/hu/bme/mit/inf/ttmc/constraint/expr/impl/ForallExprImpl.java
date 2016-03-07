package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class ForallExprImpl extends AbstractQuantifiedExpr implements ForallExpr {

	private static final String OPERATOR = "Forall";

	public ForallExprImpl(Collection<? extends ParamDecl<? extends Type>> paramDecls, Expr<? extends BoolType> op) {
		super(paramDecls, op);
	}

	@Override
	public ForallExpr withOp(Expr<? extends BoolType> op) {
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
		throw new UnsupportedOperationException();
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
