package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.dsl.Environment;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslBaseVisitor;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.CompoundInitialiserContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.InitialiserContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.SimpleInitialiserContext;

final class XtaInitialiser {

	private final Scope scope;
	private final InitialiserContext context;

	public XtaInitialiser(final Scope scope, final InitialiserContext context) {
		this.scope = checkNotNull(scope);
		this.context = checkNotNull(context);
	}

	public Expr<?> instantiate(final Type type, final Environment env) {
		final InitialiserInstantiationVisitor visitor = new InitialiserInstantiationVisitor(env);
		final Expr<?> expr = context.accept(visitor);
		return expr;
	}

	private final class InitialiserInstantiationVisitor extends XtaDslBaseVisitor<Expr<?>> {
		private final Environment env;

		public InitialiserInstantiationVisitor(final Environment env) {
			this.env = checkNotNull(env);
		}

		@Override
		public Expr<?> visitSimpleInitialiser(final SimpleInitialiserContext ctx) {
			final XtaExpression expression = new XtaExpression(scope, ctx.fExpression);
			final Expr<?> expr = expression.instantiate(env);
			return expr;
		}

		@Override
		public Expr<?> visitCompoundInitialiser(final CompoundInitialiserContext ctx) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

	}

}
