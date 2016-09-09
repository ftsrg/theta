package hu.bme.mit.inf.theta.formalism.sts.dsl.impl;

import static hu.bme.mit.inf.theta.formalism.sts.dsl.impl.StsDslHelper.createBoolExpr;
import static hu.bme.mit.inf.theta.formalism.sts.dsl.impl.StsDslHelper.createConstDefs;
import static hu.bme.mit.inf.theta.formalism.sts.dsl.impl.StsDslHelper.declareConstDecls;
import static hu.bme.mit.inf.theta.formalism.sts.dsl.impl.StsDslHelper.declareVarDecls;

import java.util.List;

import hu.bme.mit.inf.theta.common.dsl.BasicScope;
import hu.bme.mit.inf.theta.common.dsl.Scope;
import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.model.Assignment;
import hu.bme.mit.inf.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.inf.theta.core.model.impl.NestedAssignmentImpl;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.formalism.sts.dsl.gen.StsDslParser.PropDeclContext;
import hu.bme.mit.inf.theta.formalism.sts.dsl.gen.StsDslParser.SpecContext;
import hu.bme.mit.inf.theta.formalism.sts.dsl.gen.StsDslParser.StsContext;
import hu.bme.mit.inf.theta.formalism.sts.dsl.gen.StsDslParser.StsDeclContext;
import hu.bme.mit.inf.theta.formalism.sts.dsl.impl.StsCreator.StsCreationResult;
import hu.bme.mit.inf.theta.formalism.sts.impl.StsImpl;

public final class StsSpecCreator {

	private StsSpecCreator() {
	}

	public static StsSpec createStsSpec(final SpecContext specCtx, final List<? extends Expr<?>> params) {
		final String name = specCtx.name.getText();
		final List<ParamDecl<?>> paramDecls = StsDslHelper.createParamList(specCtx.paramDecls);
		final Assignment paramAssignment = new AssignmentImpl(paramDecls, params);

		final StsSpecSymbol tcfaSpecSymbol = new StsSpecSymbol(name, paramDecls);
		final Scope scope = new BasicScope(tcfaSpecSymbol);
		declareConstDecls(scope, specCtx.constDecls);
		declareVarDecls(scope, specCtx.varDecls);
		declareEachSts(scope, specCtx.stsDecls);

		final Assignment constAssignment = createConstDefs(scope, paramAssignment, specCtx.constDecls);
		final Assignment assignment = new NestedAssignmentImpl(paramAssignment, constAssignment);

		final StsSpec spec = new StsSpec();

		createPropDecls(spec, scope, assignment, specCtx.propDecls);

		return spec;
	}

	////

	private static void declareEachSts(final Scope scope, final List<? extends StsDeclContext> tcfaDeclCtxs) {
		tcfaDeclCtxs.forEach(ctx -> declareSts(scope, ctx));
	}

	private static void declareSts(final Scope scope, final StsDeclContext stsDeclCtx) {
		final String name = stsDeclCtx.name.getText();
		final List<ParamDecl<?>> paramDecls = StsDslHelper.createParamList(stsDeclCtx.paramDecls);
		final StsSymbol symbol = new StsSymbol(name, paramDecls, scope, stsDeclCtx.def);
		scope.declare(symbol);
	}

	////

	private static void createPropDecls(final StsSpec spec, final Scope scope, final Assignment assignment,
			final List<? extends PropDeclContext> propDeclCtxs) {
		propDeclCtxs.forEach(ctx -> createPropDecl(spec, scope, assignment, ctx));
	}

	private static void createPropDecl(final StsSpec spec, final Scope scope, final Assignment assignment,
			final PropDeclContext propDeclCtx) {
		final StsContext stsCtx = propDeclCtx.system;

		final StsCreationResult creationResult = StsCreator.createSts(stsCtx, scope, assignment);

		final StsImpl.Builder stsBuilder = creationResult.getBuilder();
		final Scope stsScope = creationResult.getScope();

		final Expr<? extends BoolType> prop = createBoolExpr(stsScope, assignment, propDeclCtx.cond);
		stsBuilder.setProp(prop);

		final String name = propDeclCtx.name.getText();
		final STS sts = stsBuilder.build();
		spec.addSts(name, sts);
	}

}
