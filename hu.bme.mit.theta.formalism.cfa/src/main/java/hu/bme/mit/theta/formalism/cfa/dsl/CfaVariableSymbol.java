package hu.bme.mit.theta.formalism.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.Decls.Var;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.VarDeclContext;

final class CfaVariableSymbol implements Symbol {

	private final String name;
	private final CfaType type;

	public CfaVariableSymbol(final VarDeclContext context) {
		checkNotNull(context);
		name = context.ddecl.name.getText();
		type = new CfaType(context.ddecl.ttype);
	}

	@Override
	public String getName() {
		return name;
	}

	public VarDecl<?> instantiate() {
		return Var(name, type.instantiate());
	}

}
