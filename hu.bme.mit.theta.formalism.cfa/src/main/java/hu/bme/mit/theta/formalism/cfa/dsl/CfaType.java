package hu.bme.mit.theta.formalism.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslBaseVisitor;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.BoolTypeContext;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.IntTypeContext;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.TypeContext;

final class CfaType {

	private final TypeContext context;

	public CfaType(final TypeContext context) {
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

	private static class TypeCreatorVisitor extends CfaDslBaseVisitor<Type> {
		private static final TypeCreatorVisitor INSTANCE = new TypeCreatorVisitor();

		private TypeCreatorVisitor() {
		}

		@Override
		public Type visitBoolType(final BoolTypeContext ctx) {
			return Bool();
		}

		@Override
		public Type visitIntType(final IntTypeContext ctx) {
			return Int();
		}

	}

}
