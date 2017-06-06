package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static java.util.stream.Collectors.toCollection;

import java.util.LinkedHashSet;
import java.util.Set;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.ParameterIdContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.TypeContext;
import hu.bme.mit.theta.formalism.xta.utils.RangeType;

final class XtaParameterSymbol implements Symbol {

	private final String name;
	private final boolean reference;
	private final boolean constant;

	private final XtaType type;

	public XtaParameterSymbol(final Scope scope, final TypeContext typeContext,
			final ParameterIdContext parameterIdContext) {
		checkNotNull(typeContext);
		checkNotNull(parameterIdContext);
		name = parameterIdContext.fArrayId.fId.getText();
		reference = (parameterIdContext.fRef != null);
		constant = (typeContext.fTypePrefix.fConst != null);
		type = new XtaType(scope, typeContext, parameterIdContext.fArrayId.fArrayIndexes);

		checkArgument(constant && !reference);
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isReference() {
		return reference;
	}

	public boolean isConstant() {
		return constant;
	}

	public Type instantiateType(final Environment env) {
		checkNotNull(env);
		final Type paramType = type.instantiate(env);
		return paramType;
	}

	public Set<Expr<?>> instantiateValues(final Environment env) {
		checkState(!reference);
		final Type paramType = instantiateType(env);
		final RangeType rangeType = (RangeType) paramType;
		final Set<Expr<?>> values = rangeType.values().collect(toCollection(LinkedHashSet::new));
		return values;
	}

}
