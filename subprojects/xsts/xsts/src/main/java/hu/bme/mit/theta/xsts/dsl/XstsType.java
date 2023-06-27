package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.dsl.ParseException;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.*;
import hu.bme.mit.theta.xsts.type.XstsArrayType;
import hu.bme.mit.theta.xsts.type.XstsPrimitiveType;

import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.clocktype.ClockExprs.Clock;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

final class XstsType {

	private final SymbolTable typeTable;
	private final TypeContext context;

	public XstsType(final SymbolTable typeTable, final TypeContext context) {
		this.typeTable = checkNotNull(typeTable);
		this.context = checkNotNull(context);
	}

	public hu.bme.mit.theta.xsts.type.XstsType instantiate(final Env env) {
		final TypeCreatorVisitor typeCreatorVisitor = new TypeCreatorVisitor(typeTable,env);
		final hu.bme.mit.theta.xsts.type.XstsType result = context.accept(typeCreatorVisitor);
		if (result == null) {
			throw new AssertionError();
		} else {
			return result;
		}
	}

	private static class TypeCreatorVisitor extends XstsDslBaseVisitor<hu.bme.mit.theta.xsts.type.XstsType> {

		private final SymbolTable typeTable;
		private final Env env;

		public TypeCreatorVisitor(final SymbolTable typeTable, final Env env) {
			this.typeTable = checkNotNull(typeTable);
			this.env = checkNotNull(env);
		}

		@Override
		public hu.bme.mit.theta.xsts.type.XstsType visitCustomType(final CustomTypeContext ctx) {
			Optional<? extends Symbol> optSymbol = typeTable.get(ctx.name.getText());
			if (optSymbol.isEmpty()) {
				throw new ParseException(ctx, "Type '" + ctx.name.getText() + "' cannot be resolved");
			}
			final Symbol symbol = optSymbol.get();
			final hu.bme.mit.theta.xsts.type.XstsType xstsType = (hu.bme.mit.theta.xsts.type.XstsType) env.eval(symbol);
			return xstsType;
		}

		@Override
		public hu.bme.mit.theta.xsts.type.XstsType visitBoolType(final BoolTypeContext ctx) {
			return XstsPrimitiveType.of(Bool());
		}

		@Override
		public hu.bme.mit.theta.xsts.type.XstsType visitIntType(final IntTypeContext ctx) {
			return XstsPrimitiveType.of(Int());
		}

		@Override
		public hu.bme.mit.theta.xsts.type.XstsType visitArrayType(final ArrayTypeContext ctx) {
			final hu.bme.mit.theta.xsts.type.XstsType indexType = ctx.indexType.accept(this);
			final hu.bme.mit.theta.xsts.type.XstsType elemType = ctx.elemType.accept(this);
			return XstsArrayType.of(indexType, elemType);
		}

		@Override
		public hu.bme.mit.theta.xsts.type.XstsType visitClockType(final ClockTypeContext ctx) {
			return XstsPrimitiveType.of(Clock());
		}

	}

}
