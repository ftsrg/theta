package hu.bme.mit.inf.ttmc.core.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.common.dsl.BasicScope;
import hu.bme.mit.inf.ttmc.common.dsl.Scope;
import hu.bme.mit.inf.ttmc.common.dsl.Symbol;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;

public abstract class ParametricSymbol extends BasicScope implements Symbol {

	private final String name;
	private final List<ParamDecl<?>> paramDecls;

	public ParametricSymbol(final Scope enclosingScope, final String name,
			final List<? extends ParamDecl<?>> paramDecls) {
		super(enclosingScope);
		this.name = checkNotNull(name);
		this.paramDecls = ImmutableList.copyOf(checkNotNull(paramDecls));
		declareParams(paramDecls);
	}

	private void declareParams(final List<? extends ParamDecl<?>> paramDecls) {
		paramDecls.forEach(d -> declare(new DeclSymbol(d)));
	}

	@Override
	public String getName() {
		return name;
	}

	public List<ParamDecl<?>> getParamDecls() {
		return paramDecls;
	}

}
