package hu.bme.mit.theta.formalism.tcfa.dsl;

import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.createConstDefs;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.declareConstDecls;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.declareVarDecls;
import static hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslHelper.resolveTcfa;

import java.util.List;

import hu.bme.mit.theta.common.dsl.BasicScope;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.theta.core.model.impl.NestedAssignmentImpl;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.SpecContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.TcfaDeclContext;

public final class TcfaSpecCreator {

	private TcfaSpecCreator() {
	}

	public static TcfaSpec createTcfaSpec(final SpecContext specCtx, final List<? extends Expr<?>> params) {
		final String name = specCtx.name.getText();
		final List<ParamDecl<?>> paramDecls = TcfaDslHelper.createParamList(specCtx.paramDecls);
		final Assignment paramAssignment = new AssignmentImpl(paramDecls, params);

		final TcfaSpecSymbol tcfaSpecSymbol = new TcfaSpecSymbol(name, paramDecls);
		final Scope scope = new BasicScope(tcfaSpecSymbol);
		declareConstDecls(scope, specCtx.constDecls);
		declareVarDecls(scope, specCtx.varDecls);
		declareTcfas(scope, specCtx.tcfaDecls);

		final Assignment constAssignment = createConstDefs(scope, paramAssignment, specCtx.constDecls);
		final Assignment assignment = new NestedAssignmentImpl(paramAssignment, constAssignment);

		final TcfaSpec spec = new TcfaSpec();

		createTcfas(spec, scope, assignment, specCtx.tcfaDecls);

		return spec;
	}

	////

	private static void declareTcfas(final Scope scope, final List<? extends TcfaDeclContext> tcfaDeclCtxs) {
		tcfaDeclCtxs.forEach(ctx -> declareTcfa(scope, ctx));
	}

	private static void declareTcfa(final Scope scope, final TcfaDeclContext tcfaDeclCtx) {
		final String name = tcfaDeclCtx.name.getText();
		final List<ParamDecl<?>> paramDecls = TcfaDslHelper.createParamList(tcfaDeclCtx.paramDecls);
		final TcfaSymbol symbol = new TcfaSymbol(name, paramDecls, scope, tcfaDeclCtx.def);
		scope.declare(symbol);
	}

	////

	private static void createTcfas(final TcfaSpec spec, final Scope scope, final Assignment assignment,
			final List<? extends TcfaDeclContext> tcfaDeclCtxs) {
		for (final TcfaDeclContext tcfaDeclCtx : tcfaDeclCtxs) {
			final String name = tcfaDeclCtx.name.getText();
			final TcfaSymbol symbol = resolveTcfa(scope, name);
			final TCFA tcfa = TcfaCreator.createTcfa(symbol, assignment);
			spec.addTcfa(name, tcfa);
		}
	}

}
