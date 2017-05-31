package hu.bme.mit.theta.formalism.sts.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.Types.Array;
import static hu.bme.mit.theta.core.type.Types.Bool;
import static hu.bme.mit.theta.core.type.Types.Func;
import static hu.bme.mit.theta.core.type.Types.Int;
import static hu.bme.mit.theta.core.type.Types.Rat;
import static java.util.stream.Collectors.toList;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslBaseVisitor;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.ArrayTypeContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.BoolTypeContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.FuncTypeContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.IntTypeContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.RatTypeContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.TypeListContext;

final class StsTypeCreatorVisitor extends StsDslBaseVisitor<Type> {

	private static final StsTypeCreatorVisitor INSTANCE = new StsTypeCreatorVisitor();

	StsTypeCreatorVisitor() {
	}

	public static StsTypeCreatorVisitor getInstance() {
		return INSTANCE;
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
