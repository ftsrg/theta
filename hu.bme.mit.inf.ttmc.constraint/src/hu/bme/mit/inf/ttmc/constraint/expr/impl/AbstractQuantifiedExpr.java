package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.QuantifiedExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractQuantifiedExpr extends AbstractUnaryExpr<BoolType, BoolType> implements QuantifiedExpr {

	private final List<ParamDecl<? extends Type>> paramDecls;

	protected AbstractQuantifiedExpr(final Collection<? extends ParamDecl<? extends Type>> paramDecls,
			final Expr<? extends BoolType> op) {
		super(op);
		this.paramDecls = ImmutableList.copyOf(checkNotNull(paramDecls));
	}

	@Override
	public List<ParamDecl<? extends Type>> getParamDecls() {
		return paramDecls;
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean equals(Object obj) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getOperatorString());

		final StringJoiner sj = new StringJoiner(", ", "[", "]");
		for (ParamDecl<?> varDecl : paramDecls) {
			sj.add(varDecl.toString());
		}
		sb.append(sj.toString());

		sb.append("(");
		sb.append(getOp().toString());
		sb.append(")");

		return sb.toString();
	}

}
