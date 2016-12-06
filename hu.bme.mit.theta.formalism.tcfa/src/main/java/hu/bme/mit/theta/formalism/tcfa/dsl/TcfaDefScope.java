package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.createConstDecl;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.createVarDecl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
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
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.tcfa.SimpleTcfa;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ConstDeclContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.DefTcfaContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.EdgeContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.LocContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.VarDeclContext;

final class TcfaDefScope implements Scope {

	private final DefTcfaContext defTcfaContext;

	private final Scope enclosingScope;
	private final Assignment assignment;
	private final SymbolTable symbolTable;

	private final SimpleTcfa tcfa;

	private TcfaDefScope(final Scope enclosingScope, final Assignment assignment, final DefTcfaContext defTcfaContext) {
		checkNotNull(assignment);
		this.enclosingScope = checkNotNull(enclosingScope);
		this.defTcfaContext = checkNotNull(defTcfaContext);
		symbolTable = new SymbolTable();

		declareConsts();
		declareVars();

		// TODO Handle recursive constant definitions
		final Assignment constAssignment = TcfaDslHelper.createConstDefs(this, assignment, defTcfaContext.constDecls);
		this.assignment = NestedAssignment.create(assignment, constAssignment);

		tcfa = new SimpleTcfa();

		createLocs();
		createEdges();
	}

	public static TcfaDefScope create(final Scope enclosingScope, final Assignment assignment,
			final DefTcfaContext defTcfaContext) {
		return new TcfaDefScope(enclosingScope, assignment, defTcfaContext);
	}

	////

	public TCFA getTcfa() {
		return tcfa;
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

	private void declareConsts() {
		defTcfaContext.constDecls.forEach(this::declareConst);
	}

	private void declareConst(final ConstDeclContext constDeclContext) {
		final ConstDecl<?> constDecl = createConstDecl(constDeclContext);
		final Symbol symbol = DeclSymbol.of(constDecl);
		symbolTable.add(symbol);
	}

	private void declareVars() {
		defTcfaContext.varDecls.forEach(this::declareVar);
	}

	private void declareVar(final VarDeclContext varDeclContext) {
		final VarDecl<?> varDecl = createVarDecl(varDeclContext);
		final Symbol symbol = DeclSymbol.of(varDecl);
		symbolTable.add(symbol);
	}

	private void createLocs() {
		defTcfaContext.locs.forEach(this::createLoc);
	}

	private void createLoc(final LocContext locContext) {
		final String name = locContext.name.getText();
		final boolean urgent = (locContext.urgent != null);
		final boolean init = (locContext.init != null);

		final Collection<Expr<? extends BoolType>> invars = TcfaDslHelper.createBoolExprList(this, assignment,
				locContext.invars);
		final Collection<Expr<? extends BoolType>> simplifiedInvars = new ArrayList<>();
		for (final Expr<? extends BoolType> invar : invars) {
			simplifiedInvars.add(ExprUtils.simplify(invar));
		}

		final TcfaLoc loc = tcfa.createLoc(name, urgent, simplifiedInvars);
		if (init) {
			checkArgument(tcfa.getInitLoc() == null);
			tcfa.setInitLoc(loc);
		}

		final Symbol symbol = TcfaLocSymbol.of(loc);
		symbolTable.add(symbol);
	}

	private void createEdges() {
		defTcfaContext.edges.forEach(this::createEdge);
	}

	private void createEdge(final EdgeContext edgeContext) {
		final TcfaLocSymbol sourceSymbol = resolveLoc(edgeContext.source.getText());
		final TcfaLocSymbol targetSymbol = resolveLoc(edgeContext.target.getText());
		final TcfaLoc source = sourceSymbol.geLoc();
		final TcfaLoc target = targetSymbol.geLoc();
		final List<Stmt> stmts = TcfaDslHelper.createStmtList(this, assignment, edgeContext.stmtList);
		tcfa.createEdge(source, target, stmts);
	}

	private TcfaLocSymbol resolveLoc(final String name) {
		final Optional<? extends Symbol> optSymbol = resolve(name);
		checkArgument(optSymbol.isPresent());
		final Symbol symbol = optSymbol.get();
		checkArgument(symbol instanceof TcfaLocSymbol);
		final TcfaLocSymbol locSymbol = (TcfaLocSymbol) symbol;
		return locSymbol;
	}

}
