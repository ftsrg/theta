package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collections;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.IteratorDeclContext;

final class XtaIteratorSymbol implements Symbol {

	private final String name;
	@SuppressWarnings("unused")
	private final XtaType type;

	public XtaIteratorSymbol(final Scope scope, final IteratorDeclContext context) {
		checkNotNull(context);
		name = context.fId.getText();
		type = new XtaType(scope, context.fType, Collections.emptyList());
	}

	@Override
	public String getName() {
		return name;
	}

}
