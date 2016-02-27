package hu.bme.mit.inf.ttmc.constraint.z3.solver;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import com.microsoft.z3.FuncDecl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Model;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ModelImpl;
import hu.bme.mit.inf.ttmc.constraint.z3.decl.Z3Decl;

public class Z3Model extends ModelImpl {

	final ConstraintManager manager;
	final Z3TermWrapper termWrapper;

	final com.microsoft.z3.Model z3Model;

	final Map<ConstDecl<?>, Expr<?>> valMap;

	Z3Model(final ConstraintManager manager, final Z3TermWrapper termWrapper,
			final com.microsoft.z3.Model z3Model) {
		this(manager, termWrapper, z3Model, new HashMap<>());
	}

	private Z3Model(final ConstraintManager manager, final Z3TermWrapper termWrapper,
			final com.microsoft.z3.Model z3Model, final Map<? extends ConstDecl<?>, ? extends Expr<?>> valMap) {
		this.manager = checkNotNull(manager);
		this.termWrapper = checkNotNull(termWrapper);
		this.z3Model = checkNotNull(z3Model);
		checkNotNull(valMap);
		
		this.valMap = new HashMap<>(valMap);
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final ConstDecl<T> decl) {
		checkNotNull(decl);

		Expr<?> val = valMap.get(decl);

		if (val == null) {
			@SuppressWarnings("unchecked")
			final Z3Decl<T> z3Decl = (Z3Decl<T>) decl;
			final FuncDecl funcDecl = z3Decl.getSymbol();
			
			final com.microsoft.z3.Expr term = z3Model.getConstInterp(funcDecl);
			if (term != null) {
				val = termWrapper.wrap(term);
				valMap.put(decl, val);
			}
		}

		@SuppressWarnings("unchecked")
		Expr<T> tVal = (Expr<T>) val;
		return Optional.ofNullable(tVal);
	}

	@Override
	public Model with(Map<? extends ConstDecl<?>, ? extends Expr<?>> mapping) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public Model without(Collection<? extends ConstDecl<?>> constDecls) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

}
