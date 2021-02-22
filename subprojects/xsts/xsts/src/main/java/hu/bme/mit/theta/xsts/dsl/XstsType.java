package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.dsl.ParseException;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.*;

import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

final class XstsType {

	private final Scope scope;
	private final TypeContext context;

	public XstsType(final Scope scope, final TypeContext context) {
		this.scope = checkNotNull(scope);
		this.context = checkNotNull(context);
	}

	public Type instantiate(final Env env) {
		final TypeCreatorVisitor typeCreatorVisitor = new TypeCreatorVisitor(scope,env);
		final Type result = context.accept(typeCreatorVisitor);
		if (result == null) {
			throw new AssertionError();
		} else {
			return result;
		}
	}

	private static class TypeCreatorVisitor extends XstsDslBaseVisitor<Type> {

		private final Scope scope;
		private final Env env;

		public TypeCreatorVisitor(final Scope scope, final Env env) {
			this.scope = checkNotNull(scope);
			this.env = checkNotNull(env);
		}

		@Override
		public Type visitCustomType(CustomTypeContext ctx) {
			Optional<? extends Symbol> optSymbol = scope.resolve(ctx.name.getText());
			if (optSymbol.isEmpty()) {
				throw new ParseException(ctx, "Type '" + ctx.name.getText() + "' cannot be resolved");
			}
			final Symbol symbol = optSymbol.get();
			final Type type = (Type) env.eval(symbol);
			return type;
		}

		@Override
		public Type visitBoolType(final BoolTypeContext ctx) {
			return Bool();
		}

		@Override
		public Type visitIntType(final IntTypeContext ctx) {
			return Int();
		}

		@Override
		public Type visitArrayType(final ArrayTypeContext ctx) {
			final Type indexType = ctx.indexType.accept(this);
			final Type elemType = ctx.elemType.accept(this);
			return Array(indexType, elemType);
		}

	}

}
