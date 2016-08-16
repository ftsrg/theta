package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.List;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.common.dsl.GlobalScope;
import hu.bme.mit.inf.ttmc.common.dsl.Scope;
import hu.bme.mit.inf.ttmc.common.dsl.Symbol;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.SpecContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.TcfaContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.TcfaDeclContext;

public final class TcfaSpecCreator {

	private TcfaSpecCreator() {
	}

	public static TcfaSpec createTcfaSpec(final SpecContext ctx) {
		final Scope scope = new GlobalScope();
		final TcfaSpec spec = new TcfaSpec();

		TcfaDslHelper.declareConstDecls(scope, ctx.constDecls);
		TcfaDslHelper.declareVarDecls(scope, ctx.varDecls);
		createTcfas(spec, scope, ctx.tcfaDecls);

		return spec;
	}

	private static void createTcfas(final TcfaSpec spec, final Scope scope,
			final List<? extends TcfaDeclContext> tcfaDeclCtxs) {
		declareTcfas(scope, tcfaDeclCtxs);

		for (final TcfaDeclContext tcfaDeclCtx : tcfaDeclCtxs) {
			final String name = tcfaDeclCtx.name.getText();
			final TcfaSymbol tcfaSymbol = resolveTcfa(scope, name);
			final TCFA tcfa = createTcfa(tcfaSymbol, tcfaDeclCtx.def);
			spec.addTcfa(name, tcfa);
		}
	}

	private static TcfaSymbol resolveTcfa(final Scope scope, final String name) {
		final Optional<Symbol> optSymbol = scope.resolve(name);

		checkArgument(optSymbol.isPresent());
		final Symbol symbol = optSymbol.get();

		checkArgument(symbol instanceof TcfaSymbol);
		final TcfaSymbol tcfaSymbol = (TcfaSymbol) symbol;
		return tcfaSymbol;
	}

	private static void declareTcfas(final Scope scope, final List<? extends TcfaDeclContext> tcfaDeclCtxs) {
		tcfaDeclCtxs.forEach(ctx -> declareTcfa(scope, ctx));
	}

	private static void declareTcfa(final Scope scope, final TcfaDeclContext tcfaDeclCtx) {
		final String name = tcfaDeclCtx.name.getText();
		final List<ParamDecl<?>> paramDecls = TcfaDslHelper.createParamList(tcfaDeclCtx.paramDecls);
		final Symbol symbol = new TcfaSymbol(scope, name, paramDecls);
		scope.declare(symbol);
	}

	private static TCFA createTcfa(final Scope scope, final TcfaContext tcfaContext) {
		return tcfaContext.accept(new TcfaCreatorVisitor(scope));
	}

}
