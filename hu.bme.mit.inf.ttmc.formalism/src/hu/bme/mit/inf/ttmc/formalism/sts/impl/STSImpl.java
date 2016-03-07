package hu.bme.mit.inf.ttmc.formalism.sts.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Symbolic Transition System (STS) implementation.
 * @author Akos
 *
 */
public class STSImpl implements STS {

	private final Collection<VarDecl<? extends Type>> vars;
	private final Expr<? extends BoolType> init;
	private final Expr<? extends BoolType> invar;
	private final Expr<? extends BoolType> trans;
	
	/**
	 * Constructor.
	 * @param vars Collection of variables
	 * @param init Initial constraint
	 * @param invar Invariant constraint
	 * @param trans Transition relation constraint
	 */
	public STSImpl(Collection<VarDecl<? extends Type>> vars, Expr<? extends BoolType> init,
			Expr<? extends BoolType> invar, Expr<? extends BoolType> trans) {
		checkNotNull(vars);
		this.vars = new ArrayList<>(vars);
		this.init = checkNotNull(init);
		this.invar = checkNotNull(invar);
		this.trans = checkNotNull(trans);
	}

	@Override
	public Collection<VarDecl<? extends Type>> getVars() {
		return Collections.unmodifiableCollection(vars);
	}

	@Override
	public Expr<? extends BoolType> getInit() {
		return init;
	}

	@Override
	public Expr<? extends BoolType> getInvar() {
		return invar;
	}

	@Override
	public Expr<? extends BoolType> getTrans() {
		return trans;
	}
	
	/**
	 * Builder class for Symbolic Transition Systems (STS).
	 * @author Akos
	 */
	public static class Builder {
		private final List<VarDecl<? extends Type>> vars;
		private final List<Expr<? extends BoolType>> init;
		private final List<Expr<? extends BoolType>> invar;
		private final List<Expr<? extends BoolType>> trans;
		
		/**
		 * Constructor.
		 */
		public Builder() {
			vars = new ArrayList<>();
			init = new ArrayList<>();
			invar = new ArrayList<>();
			trans = new ArrayList<>();
		}
		
		/**
		 * Add a variable declaration.
		 * @param varDecl Variable declaration
		 * @return Builder instance
		 */
		public Builder addVar(VarDecl<? extends Type> varDecl) {
			vars.add(checkNotNull(varDecl));
			return this;
		}
		
		/**
		 * Add variable declarations.
		 * @param vars Variable declarations
		 * @return Builder instance
		 */
		public Builder addVar(Collection<VarDecl<? extends Type>> vars) {
			vars.addAll(checkNotNull(vars));
			return this;
		}
		
		/**
		 * Add an initial constraint. Individual initial constraints will be joined into an AND expression.
		 * @param expr Initial constraint
		 * @return Builder instance
		 */
		public Builder addInit(Expr<? extends BoolType> expr) {
			init.add(checkNotNull(expr));
			return this;
		}
		
		/**
		 * Add initial constraints. Individual initial constraints will be joined into an AND expression.
		 * @param init Initial constraints
		 * @return Builder instance
		 */
		public Builder addInit(Collection<Expr<? extends BoolType>> init) {
			this.init.addAll(checkNotNull(init));
			return this;
		}
		
		/**
		 * Add an invariant constraint. Individual invariant constraints will be joined into an AND expression.
		 * @param expr Invariant constraint
		 * @return Builder instance
		 */
		public Builder addInvar(Expr<? extends BoolType> expr) {
			invar.add(checkNotNull(expr));
			return this;
		}
		
		/**
		 * Add invariant constraints. Individual invariant constraints will be joined into an AND expression.
		 * @param invar Invariant constraints
		 * @return Builder instance
		 */
		public Builder addInvar(Collection<Expr<? extends BoolType>> invar) {
			this.invar.addAll(checkNotNull(invar));
			return this;
		}
		
		/**
		 * Add a transition constraint. Individual transition constraints will be joined into an AND expression.
		 * @param expr Transition constraint
		 * @return Builder instance
		 */
		public Builder addTrans(Expr<? extends BoolType> expr) {
			trans.add(checkNotNull(expr));
			return this;
		}
		
		/**
		 * Add transition constraints. Individual transition constraints will be joined into an AND expression.
		 * @param trans Transition constraints
		 * @return Builder instance
		 */
		public Builder addTrans(Collection<Expr<? extends BoolType>> trans) {
			this.trans.addAll(checkNotNull(trans));
			return this;
		}
		
		/**
		 * Build the Symbolic Transition System (STS)
		 * @param manager Constraint manager (required to create an AND expression from the individual constraints)
		 * @return Symbolic Transition System
		 */
		public STS build(ConstraintManager manager) {
			return new STSImpl(
					vars,
					init.size() == 1 ? init.get(0) : manager.getExprFactory().And(init),
					invar.size() == 1 ? invar.get(0) : manager.getExprFactory().And(invar),
					trans.size() == 1 ? trans.get(0) : manager.getExprFactory().And(trans));
		}
	}

}
