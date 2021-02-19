package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.VariableDeclarationContext;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.Decls.Var;

public class XstsVariableSymbol implements Symbol {

	private final String name;
	private final XstsType type;

	public XstsVariableSymbol(final SymbolTable typeTable, final VariableDeclarationContext context) {
		checkNotNull(context);
		name = context.name.getText();
		type = new XstsType(typeTable,context.ttype);
	}

	@Override
	public String getName() {
		return name;
	}

	public VarDecl<?> instantiate(Env env) {
		return Var(name, type.instantiate(env));
	}
}
