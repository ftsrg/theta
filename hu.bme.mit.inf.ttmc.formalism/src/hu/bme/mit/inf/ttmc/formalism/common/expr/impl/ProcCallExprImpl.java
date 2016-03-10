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

	private final static int HASHSEED = 1471;
	private volatile int hashCode = 0;

	private final Expr<? extends ProcType<? extends ReturnType>> proc;
	private final ImmutableList<Expr<?>> params;

	public ProcCallExprImpl(final Expr<? extends ProcType<? extends ReturnType>> proc,
			final List<? extends Expr<?>> params) {
		this.proc = checkNotNull(proc);
		this.params = ImmutableList.copyOf(checkNotNull(params));
	}

	@Override
	public Expr<? extends ProcType<? extends ReturnType>> getProc() {
		return proc;
	}

	@Override
	public Collection<? extends Expr<? extends Type>> getParams() {
		return params;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 31 * hashCode + proc.hashCode();
			hashCode = 31 * hashCode + params.hashCode();
		}

		return hashCode;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final ProcCallExprImpl<?> that = (ProcCallExprImpl<?>) obj;
			return this.proc.equals(that.proc) && this.params.equals(that.params);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(proc.toString());
		sb.append("(");
		final String prefix = sb.toString();
		final String suffix = ")";
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (Expr<? extends Type> param : params) {
			sj.add(param.toString());
		}
		return sj.toString();
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		if (visitor instanceof ProcCallExprVisitor<?, ?>) {
			final ProcCallExprVisitor<? super P, ? extends R> sVisitor = (ProcCallExprVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}
}
