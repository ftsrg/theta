package hu.bme.mit.inf.ttmc.formalism.common.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.ProcCallExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

public class ProcCallExprImpl<ReturnType extends Type> implements ProcCallExpr<ReturnType> {

	private final static int HASH_SEED = 1471;
	private volatile int hashCode = 0;

	private final Expr<? extends ProcType<? extends ReturnType>> proc;
	private final ImmutableList<Expr<?>> params;

	public ProcCallExprImpl(final Expr<? extends ProcType<? extends ReturnType>> proc,
			final List<? extends Expr<?>> params) {
		this.proc = checkNotNull(proc);
		this.params = ImmutableList.copyOf(checkNotNull(params));
	}

	@Override
	public final Expr<? extends ProcType<? extends ReturnType>> getProc() {
		return proc;
	}

	@Override
	public final Collection<? extends Expr<? extends Type>> getParams() {
		return params;
	}

	@Override
	public final ReturnType getType() {
		return getProc().getType().getReturnType();
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		if (visitor instanceof ProcCallExprVisitor<?, ?>) {
			final ProcCallExprVisitor<? super P, ? extends R> sVisitor = (ProcCallExprVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + proc.hashCode();
			result = 31 * result + params.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ProcCallExpr<?>) {
			final ProcCallExpr<?> that = (ProcCallExpr<?>) obj;
			return this.getProc().equals(that.getProc()) && this.getParams().equals(that.getParams());
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(proc);
		sb.append("(");
		final String prefix = sb.toString();
		final String suffix = ")";
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (final Expr<? extends Type> param : params) {
			sj.add(param.toString());
		}
		return sj.toString();
	}

}
