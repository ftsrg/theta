package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.*;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

final class XstsType {

	private final TypeContext context;

	public XstsType(final TypeContext context) {
		this.context = checkNotNull(context);
	}

	public Type instantiate() {
		final Type result = TypeCreatorVisitor.INSTANCE.visit(context);
		if (result == null) {
			throw new AssertionError();
		} else {
			return result;
		}
	}

	private static class TypeCreatorVisitor extends XstsDslBaseVisitor<Type> {
		private static final TypeCreatorVisitor INSTANCE = new TypeCreatorVisitor();

		private TypeCreatorVisitor() {
		}

		@Override
		public Type visitCustomType(CustomTypeContext ctx) {
			throw new UnsupportedOperationException("TODO");
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
