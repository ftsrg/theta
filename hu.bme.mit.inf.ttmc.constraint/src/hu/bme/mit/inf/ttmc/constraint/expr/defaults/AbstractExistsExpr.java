package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractExistsExpr extends AbstractQuantifiedExpr implements ExistsExpr {

	private static final String OPERATOR = "Exists";

	public AbstractExistsExpr(final Collection<? extends ParamDecl<? extends Type>> paramDecls,
			final Expr<? extends BoolType> op) {
		super(paramDecls, op);
	}

	@Override
	public ExistsExpr withOp(final Expr<? extends BoolType> op) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
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

}
