package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.utils.impl.ExprUtils.simplify;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.createConstDefs;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.declareConstDecls;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.declareVarDecls;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.resolveTcfa;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.dsl.BasicScope;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.theta.core.model.impl.NestedAssignmentImpl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.tcfa.NetworkTcfa;
import hu.bme.mit.theta.formalism.tcfa.SimpleTcfa;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslBaseVisitor;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.DefTcfaContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.EdgeContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.LocContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ParenTcfaContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ProdTcfaContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.RefTcfaContext;

final class TcfaCreator {

	private TcfaCreator() {
	}

	public static TCFA createTcfa(final TcfaSymbol symbol, final Assignment assignment) {
		return symbol.getTcfaCtx().accept(new TcfaCreatorVisitor(symbol, assignment));
	}

	private static final class TcfaCreatorVisitor extends TcfaDslBaseVisitor<TCFA> {

		private Scope currentScope;
		private Assignment assignment;

		private TcfaCreatorVisitor(final Scope scope, final Assignment assignment) {
			currentScope = checkNotNull(scope);
			this.assignment = checkNotNull(assignment);
		}

		////

		@Override
		public TCFA visitDefTcfa(final DefTcfaContext ctx) {
			final SimpleTcfa tcfa = new SimpleTcfa();

			push();

			declareConstDecls(currentScope, ctx.constDecls);
			declareVarDecls(currentScope, ctx.varDecls);
			createLocs(tcfa, currentScope, ctx.locs);
			createEdges(tcfa, currentScope, ctx.edges);

			final Assignment constAssignment = createConstDefs(currentScope, assignment, ctx.constDecls);
			assignment = new NestedAssignmentImpl(assignment, constAssignment);

			pop();

			return tcfa;
		}

		private void push() {
			currentScope = new BasicScope(currentScope);
		}

		private void pop() {
			checkState(currentScope.enclosingScope().isPresent());
			currentScope = currentScope.enclosingScope().get();
		}

		private void createLocs(final SimpleTcfa tcfa, final Scope scope, final List<? extends LocContext> locCtxs) {
			locCtxs.forEach(locCtx -> createLoc(tcfa, scope, locCtx));
		}

		private void createLoc(final SimpleTcfa tcfa, final Scope scope, final LocContext locCtx) {
			final String name = locCtx.name.getText();
			final boolean urgent = (locCtx.urgent != null);
			final boolean init = (locCtx.init != null);

			final Collection<Expr<? extends BoolType>> invars = TcfaDslHelper.createBoolExprList(scope, assignment,
					locCtx.invars);

			final TcfaLoc loc = tcfa.createLoc(name, urgent, invars);
			if (init) {
				checkArgument(tcfa.getInitLoc() == null);
				tcfa.setInitLoc(loc);
			}

			final Symbol symbol = new TcfaLocSymbol(loc);
			scope.declare(symbol);
		}

		private void createEdges(final SimpleTcfa tcfa, final Scope scope, final List<? extends EdgeContext> edgeCtxs) {
			edgeCtxs.forEach(edgeCtx -> createEdge(tcfa, scope, edgeCtx));
		}

		private void createEdge(final SimpleTcfa tcfa, final Scope scope, final EdgeContext edgeCtx) {
			final TcfaLocSymbol sourceSymbol = resolveLoc(scope, edgeCtx.source.getText());
			final TcfaLocSymbol targetSymbol = resolveLoc(scope, edgeCtx.target.getText());
			final TcfaLoc source = sourceSymbol.geLoc();
			final TcfaLoc target = targetSymbol.geLoc();
			final List<Stmt> stmts = TcfaDslHelper.createStmtList(scope, assignment, edgeCtx.stmtList);
			tcfa.createEdge(source, target, stmts);
		}

		private static TcfaLocSymbol resolveLoc(final Scope scope, final String name) {
			final Optional<Symbol> optSymbol = scope.resolve(name);

			checkArgument(optSymbol.isPresent());
			final Symbol symbol = optSymbol.get();

			checkArgument(symbol instanceof TcfaLocSymbol);
			final TcfaLocSymbol locSymbol = (TcfaLocSymbol) symbol;

			return locSymbol;
		}

		////

		@Override
		public TCFA visitRefTcfa(final RefTcfaContext ctx) {
			final TcfaSymbol symbol = resolveTcfa(currentScope, ctx.ref.getText());
			final List<ParamDecl<?>> paramDecls = symbol.getParamDecls();

			final List<Expr<?>> paramsToEval = TcfaDslHelper.createExprList(currentScope, assignment, ctx.params);
			final List<Expr<?>> params = simplifyAll(paramsToEval, assignment);
			final Assignment paramAssignment = new AssignmentImpl(paramDecls, params);
			final Assignment newAssignment = new NestedAssignmentImpl(assignment, paramAssignment);

			final TCFA tcfa = createTcfa(symbol, newAssignment);
			return tcfa;
		}

		private static List<Expr<?>> simplifyAll(final List<? extends Expr<?>> exprs, final Assignment assignment) {
			return exprs.stream().map(e -> (Expr<?>) simplify(e, assignment)).collect(toList());
		}

		////

		@Override
		public TCFA visitProdTcfa(final ProdTcfaContext ctx) {
			if (ctx.ops.size() > 1) {
				return createProdTcfa(ctx);
			} else {
				return visitChildren(ctx);
			}
		}

		private TCFA createProdTcfa(final ProdTcfaContext ctx) {
			checkArgument(ctx.ops.size() > 1);
			final List<TCFA> tcfas = ctx.ops.stream().map(tcfaCtx -> tcfaCtx.accept(this)).collect(toList());
			return NetworkTcfa.of(tcfas);
		}

		////

		@Override
		public TCFA visitParenTcfa(final ParenTcfaContext ctx) {
			return ctx.op.accept(this);
		}
	}

}
