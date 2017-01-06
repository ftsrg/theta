package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.resolveTcfa;
import static java.util.stream.Collectors.toList;

import java.util.List;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.formalism.tcfa.NetworkTcfa;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslBaseVisitor;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.DefTcfaContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ParenTcfaContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ProdTcfaContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.RefTcfaContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.TcfaContext;

final class TcfaCreator {

	private TcfaCreator() {
	}

	public static TCFA createTcfa(final TcfaDeclSymbol scope, final Assignment assignment,
			final TcfaContext tcfaContext) {
		return tcfaContext.accept(new TcfaCreatorVisitor(scope, assignment));
	}

	private static final class TcfaCreatorVisitor extends TcfaDslBaseVisitor<TCFA> {
		private final Scope scope;
		private final Assignment assignment;

		private TcfaCreatorVisitor(final Scope scope, final Assignment assignment) {
			this.scope = checkNotNull(scope);
			this.assignment = checkNotNull(assignment);
		}

		////

		@Override
		public TCFA visitDefTcfa(final DefTcfaContext ctx) {
			final TcfaDefScope tcfaDefScope = TcfaDefScope.create(scope, assignment, ctx);
			final TCFA tcfa = tcfaDefScope.getTcfa();
			return tcfa;
		}

		@Override
		public TCFA visitRefTcfa(final RefTcfaContext ctx) {
			final TcfaDeclSymbol symbol = resolveTcfa(scope, ctx.ref.getText());
			final List<Expr<?>> args = TcfaDslHelper.createExprList(scope, assignment, ctx.params);
			return symbol.instantiate(assignment, args);
		}

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

		@Override
		public TCFA visitParenTcfa(final ParenTcfaContext ctx) {
			return ctx.op.accept(this);
		}
	}

}
