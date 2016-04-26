package hu.bme.mit.inf.ttmc.solver.z3.solver;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.FuncDecl;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.solver.z3.trasform.Z3SymbolTable;
import hu.bme.mit.inf.ttmc.solver.z3.trasform.Z3TermTransformer;
import hu.bme.mit.inf.ttmc.solver.z3.trasform.Z3TransformationManager;

class Z3Model implements Model {

	final Z3SymbolTable symbolTable;
	final Z3TransformationManager transformationManager;
	final Z3TermTransformer termTransformer;

	final com.microsoft.z3.Model z3Model;

	final Collection<ConstDecl<?>> constDecls;
	final Map<ConstDecl<?>, Expr<?>> constToExpr;

	public Z3Model(final Z3SymbolTable symbolTable, final Z3TransformationManager transformationManager,
			final Z3TermTransformer termTransformer, final com.microsoft.z3.Model z3Model) {
		this.symbolTable = symbolTable;
		this.transformationManager = transformationManager;
		this.termTransformer = termTransformer;
		this.z3Model = z3Model;

		constDecls = constDeclsOf(z3Model);
		constToExpr = new HashMap<>();
	}

	@Override
	public Collection<? extends ConstDecl<?>> getConstDecls() {
		return constDecls;
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final ConstDecl<T> decl) {
		checkNotNull(decl);

		Expr<?> val = constToExpr.get(decl);
		if (val == null) {
			final FuncDecl funcDecl = transformationManager.toSymbol(decl);
			final com.microsoft.z3.Expr term = z3Model.getConstInterp(funcDecl);
			if (term != null) {
				val = termTransformer.toExpr(term);
				constToExpr.put(decl, val);
			}
		}

		@SuppressWarnings("unchecked")
		final Expr<T> tVal = (Expr<T>) val;
		return Optional.of(tVal);
	}

	@Override
	public <T extends Type> Optional<Expr<T>> eval(final Expr<T> expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Expr<? extends BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

	private Collection<ConstDecl<?>> constDeclsOf(final com.microsoft.z3.Model z3Model) {
		final ImmutableList.Builder<ConstDecl<?>> builder = ImmutableList.builder();
		for (final com.microsoft.z3.FuncDecl symbol : z3Model.getDecls()) {
			final ConstDecl<?> constDecl = symbolTable.getConst(symbol);
			builder.add(constDecl);
		}
		return builder.build();
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "Model(", ")");
		for (final ConstDecl<?> constDecl : constDecls) {
			final StringBuilder sb = new StringBuilder();
			sb.append(constDecl.getName());
			sb.append(" <- ");
			final Optional<?> val = eval(constDecl);
			assert val.isPresent();
			sb.append(val.get());
			sj.add(sb);
		}
		return sj.toString();
	}

}
