package hu.bme.mit.inf.theta.system.ui;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.theta.constraint.model.Expression;
import hu.bme.mit.inf.theta.constraint.ui.transform.DeclTransformator;
import hu.bme.mit.inf.theta.constraint.ui.transform.ExprTransformator;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.formalism.sts.impl.StsImpl;
import hu.bme.mit.inf.theta.system.model.GloballyExpression;
import hu.bme.mit.inf.theta.system.model.InitialConstraintDefinition;
import hu.bme.mit.inf.theta.system.model.InvariantConstraintDefinition;
import hu.bme.mit.inf.theta.system.model.PropertyDeclaration;
import hu.bme.mit.inf.theta.system.model.SystemConstraintDefinition;
import hu.bme.mit.inf.theta.system.model.SystemDefinition;
import hu.bme.mit.inf.theta.system.model.SystemSpecification;
import hu.bme.mit.inf.theta.system.model.TransitionConstraintDefinition;
import hu.bme.mit.inf.theta.system.model.VariableDeclaration;
import hu.bme.mit.inf.theta.system.ui.transform.impl.SystemTransformationManager;

public class SystemModelCreator {

	public static SystemModel create(final SystemSpecification specification) {
		checkNotNull(specification);

		final Collection<STS> stss = new ArrayList<>();

		final SystemTransformationManager tManager = new SystemTransformationManager();

		for (final PropertyDeclaration propertyDeclaration : specification.getPropertyDeclarations()) {
			final SystemDefinition systemDefinition = (SystemDefinition) propertyDeclaration.getSystem();
			final STS sts = createSTS(systemDefinition, propertyDeclaration.getExpression(), tManager);

			stss.add(sts);
		}

		return new SystemModelImpl(stss);
	}

	private static STS createSTS(final SystemDefinition systemDefinition, final Expression prop,
			final SystemTransformationManager tManager) {

		final DeclTransformator dt = tManager.getDeclTransformator();
		final ExprTransformator et = tManager.getExprTransformator();

		final StsImpl.Builder builder = new StsImpl.Builder();

		if (prop instanceof GloballyExpression) {
			builder.setProp(ExprUtils.cast(et.transform(((GloballyExpression) prop).getOperand()), BoolType.class));

		} else {
			throw new UnsupportedOperationException("Currently only expressions in the form of"
					+ " G(expr) are supported, where 'expr' contains no temporal operators.");
		}

		for (final VariableDeclaration variableDeclaration : systemDefinition.getVariableDeclarations()) {
			// declarationHelper stores the created variables internally
			dt.transform(variableDeclaration);
		}

		for (final SystemConstraintDefinition constraintDef : systemDefinition.getSystemConstraintDefinitions()) {

			final Expr<? extends BoolType> expr = ExprUtils.cast(et.transform(constraintDef.getExpression()),
					BoolType.class);

			if (constraintDef instanceof InitialConstraintDefinition)
				builder.addInit(expr);
			if (constraintDef instanceof InvariantConstraintDefinition)
				builder.addInvar(expr);
			if (constraintDef instanceof TransitionConstraintDefinition)
				builder.addTrans(expr);
		}

		return builder.build();
	}

	private static class SystemModelImpl implements SystemModel {

		private final Collection<STS> stss;

		private SystemModelImpl(final Collection<STS> stss) {
			this.stss = ImmutableList.copyOf(checkNotNull(stss));
		}

		@Override
		public Collection<STS> getSTSs() {
			return stss;
		}
	}

}
