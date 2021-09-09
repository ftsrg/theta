package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.VariableDeclarationContext;

import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.Decls.Var;

public class XstsVariableSymbol implements Symbol {

	private final String name;
	private final XstsType type;
	final Map<VarDecl<?>, hu.bme.mit.theta.xsts.type.XstsType<?>> varToType;

	public XstsVariableSymbol(final SymbolTable typeTable, final Map<VarDecl<?>, hu.bme.mit.theta.xsts.type.XstsType<?>> varToType, final VariableDeclarationContext context) {
		checkNotNull(context);
		name = context.name.getText();
		this.varToType = varToType;
		type = new XstsType(typeTable,context.ttype);
	}

	@Override
	public String getName() {
		return name;
	}

	public VarDecl<?> instantiate(Env env) {
		final hu.bme.mit.theta.xsts.type.XstsType<?> xstsType = type.instantiate(env);
		final VarDecl<?> var = Var(name, xstsType.getType());
		varToType.put(var, xstsType);
		return var;
	}
}
