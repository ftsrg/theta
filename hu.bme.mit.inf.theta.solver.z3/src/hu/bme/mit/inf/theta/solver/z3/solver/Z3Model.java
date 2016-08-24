package hu.bme.mit.inf.theta.solver.z3.solver;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3.FuncDecl;

import hu.bme.mit.inf.theta.core.decl.ConstDecl;
import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.LitExpr;
import hu.bme.mit.inf.theta.core.model.Model;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.solver.z3.trasform.Z3SymbolTable;
import hu.bme.mit.inf.theta.solver.z3.trasform.Z3TermTransformer;
import hu.bme.mit.inf.theta.solver.z3.trasform.Z3TransformationManager;

class Z3Model implements Model {

	final Z3SymbolTable symbolTable;
	final Z3TransformationManager transformationManager;
	final Z3TermTransformer termTransformer;

	final com.microsoft.z3.Model z3Model;

	final Collection<ConstDecl<?>> constDecls;
	final Map<ConstDecl<?>, LitExpr<?>> constToExpr;

	public Z3Model(final Z3SymbolTable symbolTable, final Z3TransformationManager transformationManager, final Z3TermTransformer termTransformer,
			final com.microsoft.z3.Model z3Model) {
		this.symbolTable = symbolTable;
		this.transformationManager = transformationManager;
		this.termTransformer = termTransformer;
		this.z3Model = z3Model;

		constDecls = constDeclsOf(z3Model);
		constToExpr = new HashMap<>();
	}

	@Override
	public Collection<? extends ConstDecl<?>> getDecls() {
		return constDecls;
	}

	@Override
	public <DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<LitExpr<DeclType>> eval(final Decl<DeclType, DeclKind> decl) {
		checkNotNull(decl);
		checkArgument(decl instanceof ConstDecl<?>);

		@SuppressWarnings("unchecked")
		final ConstDecl<DeclType> constDecl = (ConstDecl<DeclType>) decl;

		LitExpr<?> val = constToExpr.get(constDecl);
		if (val == null) {
			final FuncDecl funcDecl = transformationManager.toSymbol(constDecl);
			final com.microsoft.z3.Expr term = z3Model.getConstInterp(funcDecl);
			if (term != null) {
				val = (LitExpr<?>) termTransformer.toExpr(term);
				constToExpr.put(constDecl, val);
			}
		}

		@SuppressWarnings("unchecked")
		final LitExpr<DeclType> tVal = (LitExpr<DeclType>) val;
		return Optional.of(tVal);
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
