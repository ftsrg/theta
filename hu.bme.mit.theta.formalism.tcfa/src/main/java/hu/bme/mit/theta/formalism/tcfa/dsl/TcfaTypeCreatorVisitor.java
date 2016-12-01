package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.impl.Types.Array;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.type.impl.Types.Func;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static hu.bme.mit.theta.core.type.impl.Types.Rat;
import static java.util.stream.Collectors.toList;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslBaseVisitor;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ArrayTypeContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.BoolTypeContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.ClockTypeContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.FuncTypeContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.IntTypeContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.RatTypeContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.TypeListContext;

final class TcfaTypeCreatorVisitor extends TcfaDslBaseVisitor<Type> {

	private static final TcfaTypeCreatorVisitor INSTANCE = new TcfaTypeCreatorVisitor();

	TcfaTypeCreatorVisitor() {
	}

	public static TcfaTypeCreatorVisitor getInstance() {
		return INSTANCE;
	}

	@Override
	public Type visitClockType(final ClockTypeContext ctx) {
		throw new UnsupportedOperationException();
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
	public Type visitRatType(final RatTypeContext ctx) {
		return Rat();
	}

	@Override
	public Type visitFuncType(final FuncTypeContext ctx) {
		final List<Type> paramTypes = createTypeList(ctx.paramTypes);

		checkArgument(paramTypes.size() == 1);
		final Type paramType = paramTypes.get(0);

		final Type resultType = ctx.returnType.accept(this);
		return Func(paramType, resultType);
	}

	@Override
	public Type visitArrayType(final ArrayTypeContext ctx) {
		final List<Type> indexTypes = createTypeList(ctx.indexTypes);

		checkArgument(indexTypes.size() == 1);
		final Type indexType = indexTypes.get(0);

		final Type elemType = ctx.elemType.accept(this);
		return Array(indexType, elemType);
	}

	private List<Type> createTypeList(final TypeListContext ctx) {
		if (ctx.types == null) {
			return Collections.emptyList();
		} else {
			final List<Type> types = ctx.types.stream().map(t -> t.accept(this)).collect(toList());
			return types;
		}
	}
}
