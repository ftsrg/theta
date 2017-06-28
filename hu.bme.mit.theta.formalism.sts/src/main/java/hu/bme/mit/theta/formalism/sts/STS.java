package hu.bme.mit.theta.formalism.sts;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

/**
 * An immutable Symbolic Transition System (STS) implementation. An STS consists
 * of an initial expression, a transition relation expression and a property
 * expression over a set of variables. An inner builder class can also be used
 * for creating an STS more conveniently.
 */
public final class STS {
	private final Collection<VarDecl<?>> vars;
	private final Expr<BoolType> init;
	private final Expr<BoolType> trans;
	private final Expr<BoolType> prop;

	/**
	 * Create a new STS from an initial expression, a transition relation and a
	 * property.
	 *
	 * @param init Initial expression
	 * @param trans Transition relation expression
	 * @param prop Property expression
	 */
	public STS(final Expr<BoolType> init, final Expr<BoolType> trans, final Expr<BoolType> prop) {
		this.init = checkNotNull(init);
		this.trans = checkNotNull(trans);
		this.prop = checkNotNull(prop);
		final Set<VarDecl<?>> tmpVars = new HashSet<>();
		ExprUtils.collectVars(init, tmpVars);
		ExprUtils.collectVars(trans, tmpVars);
		ExprUtils.collectVars(prop, tmpVars);
		this.vars = Collections.unmodifiableCollection(tmpVars);
	}

	/**
	 * Gets the collection of variables appearing in the expressions of the STS.
	 *
	 * @return
	 */
	public Collection<VarDecl<?>> getVars() {
		return vars;
	}

	/**
	 * Gets the initial expression.
	 *
	 * @return
	 */
	public Expr<BoolType> getInit() {
		return init;
	}

	/**
	 * Gets the transition relation expression.
	 *
	 * @return
	 */
	public Expr<BoolType> getTrans() {
		return trans;
	}

	/**
	 * Gets the property expression.
	 *
	 * @return
	 */
	public Expr<BoolType> getProp() {
		return prop;
	}

	/**
	 * Creates a new builder instance.
	 *
	 * @return
	 */
	public static Builder builder() {
		return new Builder();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder("STS [" + System.lineSeparator());
		sb.append("\tVars:  ").append(vars).append(System.lineSeparator());
		sb.append("\tInit:  ").append(init).append(System.lineSeparator());
		sb.append("\tTrans: ").append(trans).append(System.lineSeparator());
		sb.append("\tProp: ").append(prop).append(System.lineSeparator()).append("]");
		return sb.toString();
	}

	/**
	 * Helper class for building an STS, supporting multiple initial/transition
	 * constraints and invariants.
	 */
	public static final class Builder {
		private final Collection<Expr<BoolType>> init;
		private final Collection<Expr<BoolType>> trans;
		private Expr<BoolType> prop;

		private Builder() {
			init = new HashSet<>();
			trans = new HashSet<>();
			prop = null;
		}

		/**
		 * Add an initial expression. Multiple initial expressions will be
		 * joined into a conjunction.
		 *
		 * @param expr Expression to be added
		 */
		public Builder addInit(final Expr<BoolType> expr) {
			checkNotNull(expr);
			if (expr instanceof AndExpr) addInit(((AndExpr) expr).getOps());
			else init.add(checkNotNull(expr));
			return this;
		}

		/**
		 * Add initial expressions. Multiple initial expressions will be joined
		 * into a conjunction.
		 *
		 * @param exprs Expressions to be added
		 */
		public Builder addInit(final Iterable<? extends Expr<BoolType>> exprs) {
			checkNotNull(exprs);
			for (final Expr<BoolType> expr : exprs)
				addInit(expr);
			return this;
		}

		/**
		 * Add an invariant expression. An invariant is added both to the
		 * initial and transition expressions.
		 *
		 * @param expr Expression to be added
		 */
		public Builder addInvar(final Expr<BoolType> expr) {
			checkNotNull(expr);
			if (expr instanceof AndExpr) {
				addInvar(((AndExpr) expr).getOps());
			} else {
				addInit(expr);
				addTrans(expr);
				addTrans(Prime(expr));
			}

			return this;
		}

		/**
		 * Add invariant expressions. Invariants are added both to the initial
		 * and transition expressions.
		 *
		 * @param exprs Expressions to be added
		 */
		public Builder addInvar(final Iterable<? extends Expr<BoolType>> exprs) {
			checkNotNull(exprs);
			for (final Expr<BoolType> expr : exprs)
				addInvar(expr);
			return this;
		}

		/**
		 * Add a transition expression. Multiple transition expressions will be
		 * joined into a conjunction.
		 *
		 * @param expr Expression to be added
		 */
		public Builder addTrans(final Expr<BoolType> expr) {
			checkNotNull(expr);
			if (expr instanceof AndExpr) addTrans(((AndExpr) expr).getOps());
			else trans.add(expr);
			return this;
		}

		/**
		 * Add transition expressions. Multiple transition expressions will be
		 * joined into a conjunction.
		 *
		 * @param exprs Expressions to be added
		 */
		public Builder addTrans(final Iterable<? extends Expr<BoolType>> exprs) {
			checkNotNull(exprs);
			for (final Expr<BoolType> expr : exprs)
				addTrans(expr);
			return this;
		}

		/**
		 * Set the property expression. Previously set property will be
		 * overridden.
		 *
		 * @param expr Expression to be set as property
		 */
		public Builder setProp(final Expr<BoolType> expr) {
			checkNotNull(expr);
			this.prop = expr;
			return this;
		}

		/**
		 * Build an STS. The builder can be modified after building to get new
		 * STSs, the already built ones will not be affected.
		 *
		 * @return STS instance
		 */
		public STS build() {
			checkNotNull(prop);
			return new STS(And(init), And(trans), prop);
		}
	}
}
