package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;
import java.util.NoSuchElementException;
import java.util.Optional;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.ToStringBuilder;
import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class ExplState implements ExprState, Valuation {

	public static ExplState create(final Valuation values) {
		return new NonBottom(values);
	}

	public static ExplState createBottom() {
		return BottomLazyHolder.INSTANCE;
	}

	public abstract <ExprType extends Type> LitExpr<ExprType> getValue(final Decl<ExprType> varDecl);

	public abstract boolean isLeq(final ExplState that);

	public abstract boolean isBottom();

	////

	private static final class NonBottom extends ExplState {

		private static final int HASH_SEED = 6659;
		private final Valuation values;
		private volatile int hashCode;

		private NonBottom(final Valuation values) {
			this.values = checkNotNull(values);
		}

		@Override
		public <ExprType extends Type> LitExpr<ExprType> getValue(final Decl<ExprType> varDecl) {
			return values.eval(varDecl).get();
		}

		@Override
		public Collection<? extends Decl<?>> getDecls() {
			return values.getDecls();
		}

		@Override
		public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
			return values.eval(decl);
		}

		@Override
		public Expr<BoolType> toExpr() {
			return values.toExpr();
		}

		////

		@Override
		public boolean isLeq(final ExplState that) {
			if (that.isBottom()) {
				return false;
			}
			if (that.getDecls().size() > this.getDecls().size()) {
				return false;
			}
			for (final Decl<?> varDecl : that.getDecls()) {
				if (!this.getDecls().contains(varDecl) || !that.getValue(varDecl).equals(this.getValue(varDecl))) {
					return false;
				}
			}
			return true;
		}

		@Override
		public boolean isBottom() {
			return false;
		}

		////

		@Override
		public int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 31 * result + values.hashCode();
				hashCode = result;
			}
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj instanceof NonBottom) {
				final NonBottom that = (NonBottom) obj;
				return this.values.equals(that.values);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			final ToStringBuilder builder = ObjectUtils.toStringBuilder(ExplState.class.getSimpleName());
			for (final Decl<?> varDecl : values.getDecls()) {
				builder.add(varDecl.getName() + " = " + getValue(varDecl));
			}
			return builder.toString();
		}
	}

	private static final class Bottom extends ExplState {

		@Override
		public <ExprType extends Type> LitExpr<ExprType> getValue(final Decl<ExprType> varDecl) {
			throw new NoSuchElementException("Bottom state contains no values.");
		}

		@Override
		public Collection<? extends Decl<?>> getDecls() {
			return Collections.emptySet();
		}

		@Override
		public <DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl) {
			return Optional.empty();
		}

		@Override
		public Expr<BoolType> toExpr() {
			return BoolExprs.False();
		}

		////

		@Override
		public boolean isLeq(final ExplState that) {
			return true;
		}

		@Override
		public boolean isBottom() {
			return true;
		}

		////

		@Override
		public int hashCode() {
			return 3931;
		}

		@Override
		public boolean equals(final Object obj) {
			return obj instanceof Bottom;
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(ExplState.class.getSimpleName()).add("Bottom").toString();
		}
	}

	private static class BottomLazyHolder {
		static final Bottom INSTANCE = new Bottom();
	}
}
