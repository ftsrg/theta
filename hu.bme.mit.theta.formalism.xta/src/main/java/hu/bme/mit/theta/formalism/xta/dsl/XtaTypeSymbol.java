package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.ArrayIdContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.TypeContext;

final class XtaTypeSymbol implements Symbol {

	private final String name;
	private final XtaType type;

	public XtaTypeSymbol(final Scope scope, final TypeContext typeContext, final ArrayIdContext arrayIdContext) {
		checkNotNull(typeContext);
		checkNotNull(arrayIdContext);
		name = arrayIdContext.fId.getText();
		type = new XtaType(scope, typeContext, arrayIdContext.fArrayIndexes);
	}

	@Override
	public String getName() {
		return name;
	}

	public Type instantiate(final Environment env) {
		return type.instantiate(env);
	}

}
