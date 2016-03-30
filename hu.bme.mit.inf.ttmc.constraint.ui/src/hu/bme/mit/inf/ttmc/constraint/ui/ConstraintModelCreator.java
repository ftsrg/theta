package hu.bme.mit.inf.ttmc.constraint.ui;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.model.BasicConstraintDefinition;
import hu.bme.mit.inf.ttmc.constraint.model.ConstantDeclaration;
import hu.bme.mit.inf.ttmc.constraint.model.ConstraintSpecification;
import hu.bme.mit.inf.ttmc.constraint.model.Expression;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.ui.impl.ConstraintModelBuilder;
import hu.bme.mit.inf.ttmc.constraint.ui.impl.ConstraintModelImpl;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.ExprTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.impl.ConstraintTransformationManager;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprUtils;

public class ConstraintModelCreator {

	private ConstraintModelCreator() {
	}

	public static ConstraintModel create(final ConstraintManager manager, final ConstraintSpecification specification) {
		checkNotNull(manager);
		checkNotNull(specification);

		final ConstraintTransformationManager tManager = new ConstraintTransformationManager(manager);
		final ConstraintModelBuilder builder = ConstraintModelImpl.builder();

		addConstants(builder, specification, tManager);
		addConstraints(builder, specification, tManager);

		return builder.build();
	}

	private static void addConstants(final ConstraintModelBuilder builder, final ConstraintSpecification specification,
			final ConstraintTransformationManager manager) {
		final DeclTransformator dt = manager.getDeclTransformator();

		for (final ConstantDeclaration constantDeclaration : specification.getConstantDeclarations()) {
			@SuppressWarnings("unchecked")
			final ConstDecl<Type> constDecl = (ConstDecl<Type>) dt.transform(constantDeclaration);
			builder.addConstDecl(constDecl);
		}
	}

	private static void addConstraints(final ConstraintModelBuilder builder,
			final ConstraintSpecification specification, final ConstraintTransformationManager manager) {
		final ExprTransformator et = manager.getExprTransformator();

		for (final BasicConstraintDefinition basicConstraintDefinition : specification
				.getBasicConstraintDefinitions()) {
			final Expression expression = basicConstraintDefinition.getExpression();
			final Expr<? extends BoolType> expr = ExprUtils.cast(et.transform(expression), BoolType.class);
			final Collection<Expr<? extends BoolType>> conjuncts = ExprUtils.getConjuncts(expr);
			builder.addConstraints(conjuncts);
		}
	}

}
