package hu.bme.mit.inf.ttmc.constraint.ui;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.model.BasicConstraintDefinition;
import hu.bme.mit.inf.ttmc.constraint.model.ConstraintSpecification;
import hu.bme.mit.inf.ttmc.constraint.model.Expression;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class ConstraintModel {

	private final Collection<ConstDecl<? extends Type>> constDecls;
	private final Collection<Expr<? extends BoolType>> constraints;

	////

	private ConstraintModel(final Collection<ConstDecl<? extends Type>> constDecls,
			final Collection<Expr<? extends BoolType>> constraints) {
		this.constDecls = constDecls;
		this.constraints = constraints;
	}

	public static ConstraintModel create(final ConstraintManager manager, final ConstraintSpecification specification) {
		checkNotNull(manager);
		checkNotNull(specification);

		final ConstraintModelHelper helper = new ConstraintModelHelper(manager);

		final Collection<Expr<? extends BoolType>> constraints = new ArrayList<>();

		for (BasicConstraintDefinition basicConstraintDefinition : specification.getBasicConstraintDefinitions()) {
			final Expression expression = basicConstraintDefinition.getExpression();
			final Expr<?> expr = helper.toExpr(expression);
			final Expr<? extends BoolType> boolExpr = helper.withType(expr, BoolType.class);
			constraints.add(boolExpr);
		}

		final Collection<ConstDecl<? extends Type>> constDecls = new ArrayList<>(helper.getConstDecls());

		final ConstraintModel model = new ConstraintModel(constDecls, constraints);
		return model;
	}

	////

	public Collection<ConstDecl<?>> getConstDecls() {
		return Collections.unmodifiableCollection(constDecls);
	}

	public Collection<Expr<? extends BoolType>> getConstraints() {
		return Collections.unmodifiableCollection(constraints);
	}

}
