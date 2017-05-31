package hu.bme.mit.theta.formalism.sts.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.formalism.sts.dsl.StsDslHelper.createBoolExpr;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.PropDeclContext;

final class PropDeclSymbol implements Symbol {

	private final PropDeclContext propDeclContext;

	private final StsSpecSymbol scope;

	private final String name;

	private PropDeclSymbol(final StsSpecSymbol scope, final PropDeclContext propDeclContext) {
		this.scope = checkNotNull(scope);
		this.propDeclContext = checkNotNull(propDeclContext);
		name = propDeclContext.name.getText();
	}

	public static PropDeclSymbol create(final StsSpecSymbol scope, final PropDeclContext propDeclContext) {
		return new PropDeclSymbol(scope, propDeclContext);
	}

	////

	@Override
	public String getName() {
		return name;
	}

	////

	public STS instantiate(final Assignment assignment) {
		final StsDefScope stsDefScope = StsCreator.createSts(scope, assignment, propDeclContext.system);
		final Expr<? extends BoolType> prop = createBoolExpr(stsDefScope, assignment, propDeclContext.cond);

		final STS sts = stsDefScope.getSts();

		final STS.Builder builder = STS.builder();
		builder.addInit(sts.getInit());
		builder.addTrans(sts.getTrans());
		builder.setProp(prop);
		return builder.build();
	}

}
