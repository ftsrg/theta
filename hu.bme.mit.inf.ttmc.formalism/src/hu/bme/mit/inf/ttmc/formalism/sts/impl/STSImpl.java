package hu.bme.mit.inf.ttmc.formalism.sts.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;

import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.VarCollectorVisitor;

/**
 * Symbolic Transition System (STS) implementation.
 */
public class STSImpl implements STS {

	private final Collection<VarDecl<? extends Type>> vars;
	private final Collection<Expr<? extends BoolType>> init;
	private final Collection<Expr<? extends BoolType>> invar;
	private final Collection<Expr<? extends BoolType>> trans;
	private final Expr<? extends BoolType> prop;
	
	// Protected constructor --> use the builder
	protected STSImpl(Collection<VarDecl<? extends Type>> vars, Collection<Expr<? extends BoolType>> init,
			Collection<Expr<? extends BoolType>> invar, Collection<Expr<? extends BoolType>> trans,
			Expr<? extends BoolType> prop) {
		checkNotNull(vars);
		checkNotNull(init);
		checkNotNull(invar);
		checkNotNull(trans);
		checkNotNull(prop);
		this.vars = new ArrayList<>(vars);
		this.init = new ArrayList<>(init);
		this.invar = new ArrayList<>(invar);
		this.trans = new ArrayList<>(trans);
		this.prop = prop;
	}

	@Override
	public Collection<VarDecl<? extends Type>> getVars() {
		return Collections.unmodifiableCollection(vars);
	}

	@Override
	public Collection<Expr<? extends BoolType>> getInit() {
		return Collections.unmodifiableCollection(init);
	}

	@Override
	public Collection<Expr<? extends BoolType>> getInvar() {
		return Collections.unmodifiableCollection(invar);
	}

	@Override
	public Collection<Expr<? extends BoolType>> getTrans() {
		return Collections.unmodifiableCollection(trans);
	}
	
	@Override
	public Expr<? extends BoolType> getProp() {
		return prop;
	}
	
	public static class Builder {
		private final Collection<VarDecl<? extends Type>> vars;
		private final Collection<Expr<? extends BoolType>> init;
		private final Collection<Expr<? extends BoolType>> invar;
		private final Collection<Expr<? extends BoolType>> trans;
		private Expr<? extends BoolType> prop;
		private final VarCollectorVisitor varCollectorVisitor;
		
		public Builder() {
			vars = new HashSet<>();
			init = new HashSet<>();
			invar = new HashSet<>();
			trans = new HashSet<>();
			prop = null;
			varCollectorVisitor = new VarCollectorVisitor();
		}
		
		/**
		 * Add an initial constraint. If the constraint is an AND expression it will be split
		 * into its conjuncts. Duplicate constraints are included only once.
		 */
		public Builder addInit(Expr<? extends BoolType> expr) {
			checkNotNull(expr);
			if (expr instanceof AndExpr) addInit(((AndExpr)expr).getOps());
			else init.add(checkNotNull(expr));
			return this;
		}
		
		/**
		 * Add initial constraints. If the constraint is an AND expression it will be split
		 * into its conjuncts. Duplicate constraints are included only once.
		 */
		public Builder addInit(Collection<? extends Expr<? extends BoolType>> init) {
			checkNotNull(init);
			for (Expr<? extends BoolType> expr : init) addInit(expr);
			return this;
		}
		
		/**
		 * Add an invariant constraint. If the constraint is an AND expression it will be split
		 * into its conjuncts. Duplicate constraints are included only once.
		 */
		public Builder addInvar(Expr<? extends BoolType> expr) {
			checkNotNull(expr);
			if (expr instanceof AndExpr) addInvar(((AndExpr)expr).getOps());
			else invar.add(expr);
			return this;
		}
		
		/**
		 * Add invariant constraints. If the constraint is an AND expression it will be split
		 * into its conjuncts. Duplicate constraints are included only once.
		 */
		public Builder addInvar(Collection<? extends Expr<? extends BoolType>> invar) {
			checkNotNull(invar);
			for (Expr<? extends BoolType> expr : invar) addInvar(expr);
			return this;
		}
		
		/**
		 * Add a transition constraint. If the constraint is an AND expression it will be split
		 * into its conjuncts. Duplicate constraints are included only once.
		 */
		public Builder addTrans(Expr<? extends BoolType> expr) {
			checkNotNull(expr);
			if (expr instanceof AndExpr) addTrans(((AndExpr)expr).getOps());
			else trans.add(expr);
			return this;
		}
		
		/**
		 * Add transition constraints. If the constraint is an AND expression it will be split
		 * into its conjuncts. Duplicate constraints are included only once.
		 */
		public Builder addTrans(Collection<? extends Expr<? extends BoolType>> trans) {
			checkNotNull(trans);
			for (Expr<? extends BoolType> expr : trans) addTrans(expr);
			return this;
		}
		
		public Builder setProp(Expr<? extends BoolType> prop) {
			checkNotNull(prop);
			this.prop = prop;
			return this;
		}
		
		public STS build() {
			// Collect variables from the expressions
			for (Expr<? extends BoolType> expr : init) expr.accept(varCollectorVisitor, vars);
			for (Expr<? extends BoolType> expr : invar) expr.accept(varCollectorVisitor, vars);
			for (Expr<? extends BoolType> expr : trans) expr.accept(varCollectorVisitor, vars);
			prop.accept(varCollectorVisitor, vars);
			
			return new STSImpl(vars, init, invar, trans, prop);
		}
	}


}
