package hu.bme.mit.inf.ttmc.constraint.z3.solver;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import com.microsoft.z3.FuncDecl;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Model;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ModelImpl;
import hu.bme.mit.inf.ttmc.constraint.z3.trasform.Z3TermTransformer;
import hu.bme.mit.inf.ttmc.constraint.z3.trasform.Z3TransformationManager;

class Z3Model2 extends ModelImpl {

	final Z3TransformationManager transformationManager;
	final Z3TermTransformer termTransformer;

	final com.microsoft.z3.Model z3Model;

	final Map<ConstDecl<?>, Expr<?>> valMap;

	public Z3Model2(final Z3TransformationManager transformationManager, final Z3TermTransformer termTransformer,
			final com.microsoft.z3.Model z3Model) {
		this.transformationManager = transformationManager;
		this.termTransformer = termTransformer;
		this.z3Model = z3Model;
		this.valMap = new HashMap<>();
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final ConstDecl<T> decl) {
		checkNotNull(decl);

		Expr<?> val = valMap.get(decl);

		if (val == null) {
			final FuncDecl funcDecl = transformationManager.toSymbol(decl);
			final com.microsoft.z3.Expr term = z3Model.getConstInterp(funcDecl);
			if (term != null) {
				val = termTransformer.toExpr(term);
				valMap.put(decl, val);
			}
		}

		@SuppressWarnings("unchecked")
		final Expr<T> tVal = (Expr<T>) val;
		return Optional.ofNullable(tVal);
	}

	@Override
	public Model with(final Map<? extends ConstDecl<?>, ? extends Expr<?>> mapping) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public Model without(final Collection<? extends ConstDecl<?>> constDecls) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

}
