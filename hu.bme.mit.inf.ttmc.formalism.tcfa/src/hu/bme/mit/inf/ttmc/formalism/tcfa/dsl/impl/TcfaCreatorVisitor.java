package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.common.dsl.LocalScope;
import hu.bme.mit.inf.ttmc.common.dsl.Scope;
import hu.bme.mit.inf.ttmc.common.dsl.Symbol;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFALoc;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslBaseVisitor;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.DefTcfaContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.EdgeContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.LocContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.ParenTcfaContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.ProdTcfaContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.RefTcfaContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.impl.MutableTCFA;

public class TcfaCreatorVisitor extends TcfaDslBaseVisitor<TCFA> {

	private Scope currentScope;

	public TcfaCreatorVisitor(final Scope scope) {
		currentScope = checkNotNull(scope);
	}

	@Override
	public TCFA visitDefTcfa(final DefTcfaContext ctx) {
		final MutableTCFA tcfa = new MutableTCFA();

		push();

		TcfaDslHelper.declareConstDecls(currentScope, ctx.constDecls);
		TcfaDslHelper.declareVarDecls(currentScope, ctx.varDecls);
		createLocs(tcfa, currentScope, ctx.locs);
		createEdges(tcfa, currentScope, ctx.edges);

		pop();

		return tcfa;
	}

	private void push() {
		currentScope = new LocalScope(currentScope);
	}

	private void pop() {
		checkState(currentScope.enclosingScope().isPresent());
		currentScope = currentScope.enclosingScope().get();
	}

	private static void createLocs(final MutableTCFA tcfa, final Scope scope, final List<LocContext> locCtxs) {
		locCtxs.forEach(locCtx -> createLoc(tcfa, scope, locCtx));
	}

	private static void createLoc(final MutableTCFA tcfa, final Scope scope, final LocContext locCtx) {
		final String name = locCtx.name.getText();
		final boolean urgent = (locCtx.urgent != null);
		final Collection<Expr<? extends BoolType>> invars = TcfaDslHelper.createBoolExprList(scope, locCtx.invars);

		final TCFALoc loc = tcfa.createLoc(name, urgent, invars);
		final Symbol symbol = new TcfaLocSymbol(loc);
		scope.declare(symbol);
	}

	private static void createEdges(final MutableTCFA tcfa, final Scope scope, final List<EdgeContext> edgeCtxs) {
		edgeCtxs.forEach(edgeCtx -> createEdge(tcfa, scope, edgeCtx));
	}

	private static void createEdge(final MutableTCFA tcfa, final Scope scope, final EdgeContext edgeCtx) {
		final TCFALoc source = resolveLoc(scope, edgeCtx.source.getText());
		final TCFALoc target = resolveLoc(scope, edgeCtx.target.getText());
		final List<Stmt> stmts = TcfaDslHelper.createStmtList(scope, edgeCtx.stmtList);
		tcfa.createEdge(source, target, stmts);
	}

	private static TCFALoc resolveLoc(final Scope scope, final String name) {
		final Optional<Symbol> optSymbol = scope.resolve(name);

		checkArgument(optSymbol.isPresent());
		final Symbol symbol = optSymbol.get();

		checkArgument(symbol instanceof TcfaLocSymbol);
		final TcfaLocSymbol locSymbol = (TcfaLocSymbol) symbol;
		final TCFALoc loc = locSymbol.geLoc();

		return loc;
	}

	@Override
	public TCFA visitRefTcfa(final RefTcfaContext ctx) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public TCFA visitProdTcfa(final ProdTcfaContext ctx) {
		if (ctx.ops.size() > 1) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		} else {
			return visitChildren(ctx);
		}
	}

	@Override
	public TCFA visitParenTcfa(final ParenTcfaContext ctx) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
