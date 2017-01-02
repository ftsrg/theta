package hu.bme.mit.theta.formalism.sts.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.theta.formalism.sts.dsl.StsDslHelper.createBoolExpr;
import static hu.bme.mit.theta.formalism.sts.dsl.StsDslHelper.createConstDecl;
import static hu.bme.mit.theta.formalism.sts.dsl.StsDslHelper.createVarDecl;

import java.util.Optional;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.NestedAssignment;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.ConstDeclContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.DefStsContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.InitConstrContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.InvarConstrContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.TransConstrContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.VarDeclContext;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl;

final class StsDefScope implements Scope {

	private final DefStsContext defStsContext;

	private final Scope enclosingScope;
	private final Assignment assignment;
	private final SymbolTable symbolTable;

	private final StsImpl.Builder stsBuilder;
	private final STS sts;

	private StsDefScope(final Scope enclosingScope, final Assignment assignment, final DefStsContext defTcfaContext) {
		checkNotNull(assignment);
		this.enclosingScope = checkNotNull(enclosingScope);
		this.defStsContext = checkNotNull(defTcfaContext);
		symbolTable = new SymbolTable();

		declareConsts();
		declareVars();

		// TODO Handle recursive constant definitions
		final Assignment constAssignment = StsDslHelper.createConstDefs(this, assignment, defTcfaContext.constDecls);
		this.assignment = NestedAssignment.create(assignment, constAssignment);

		stsBuilder = new StsImpl.Builder();

		createInvarConstrs();
		createInitConstrs();
		createTransConstrs();

		// TODO Separate system and property
		stsBuilder.setProp(True());

		sts = stsBuilder.build();
	}

	public static StsDefScope create(final Scope enclosingScope, final Assignment assignment,
			final DefStsContext defTcfaContext) {
		return new StsDefScope(enclosingScope, assignment, defTcfaContext);
	}

	////

	public STS getSts() {
		return sts;
	}

	////

	@Override
	public Optional<Scope> enclosingScope() {
		return Optional.of(enclosingScope);
	}

	@Override
	public Optional<? extends Symbol> resolve(final String name) {
		final Optional<Symbol> optSymbol = symbolTable.get(name);
		if (optSymbol.isPresent()) {
			return optSymbol;
		} else {
			return enclosingScope.resolve(name);
		}
	}

	////

	private void createInvarConstrs() {
		defStsContext.invarConstrs.forEach(this::createInvarConstr);
	}

	private void createInvarConstr(final InvarConstrContext invarConstrCtx) {
		final Expr<? extends BoolType> cond = createBoolExpr(this, assignment, invarConstrCtx.cond);
		stsBuilder.addInvar(cond);
	}

	private void createInitConstrs() {
		defStsContext.initConstrs.forEach(this::createInitConstr);
	}

	private void createInitConstr(final InitConstrContext initConstrCtx) {
		final Expr<? extends BoolType> cond = createBoolExpr(this, assignment, initConstrCtx.cond);
		stsBuilder.addInit(cond);
	}

	private void createTransConstrs() {
		defStsContext.transConstrs.forEach(this::createTransConstr);
	}

	private void createTransConstr(final TransConstrContext transConstrCtx) {
		final Expr<? extends BoolType> cond = createBoolExpr(this, assignment, transConstrCtx.cond);
		stsBuilder.addTrans(cond);
	}

	////

	private void declareConsts() {
		defStsContext.constDecls.forEach(this::declareConst);
	}

	private void declareConst(final ConstDeclContext constDeclContext) {
		final ConstDecl<?> constDecl = createConstDecl(constDeclContext);
		final Symbol symbol = DeclSymbol.of(constDecl);
		symbolTable.add(symbol);
	}

	private void declareVars() {
		defStsContext.varDecls.forEach(this::declareVar);
	}

	private void declareVar(final VarDeclContext varDeclContext) {
		final VarDecl<?> varDecl = createVarDecl(varDeclContext);
		final Symbol symbol = DeclSymbol.of(varDecl);
		symbolTable.add(symbol);
	}

}
