package hu.bme.mit.inf.ttmc.constraint.ui;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.model.BasicConstraintDefinition;
import hu.bme.mit.inf.ttmc.constraint.model.ConstantDeclaration;
import hu.bme.mit.inf.ttmc.constraint.model.ConstraintSpecification;
import hu.bme.mit.inf.ttmc.constraint.model.Expression;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprUtils;

public class ConstraintModelCreator {

	private ConstraintModelCreator() {
	}
	
	public static ConstraintModel create(final ConstraintManager manager, final ConstraintSpecification specification) {
		checkNotNull(manager);
		checkNotNull(specification);

		final TypeHelper typeHelper = new TypeHelper(manager.getTypeFactory());
		final DeclarationHelper declarationHelper = new DeclarationHelper(manager.getDeclFactory(), typeHelper);
		final ExpressionHelper expressionHelper = new ExpressionHelper(manager, declarationHelper);
		
		final Collection<ConstDecl<Type>> constDecls = new ArrayList<>();
		for (ConstantDeclaration constantDeclaration : specification.getConstantDeclarations()) {
			final ConstDecl<Type> constDecl = (ConstDecl<Type>) declarationHelper.toDecl(constantDeclaration);
			constDecls.add(constDecl);
		}
		
		final Collection<Expr<? extends BoolType>> constraints = new ArrayList<>();
		for (BasicConstraintDefinition basicConstraintDefinition : specification.getBasicConstraintDefinitions()) {
			final Expression expression = basicConstraintDefinition.getExpression();
			final Expr<? extends BoolType> expr = ExprUtils.cast(manager.getTypeInferrer(), expressionHelper.toExpr(expression), BoolType.class);
			final Collection<Expr<? extends BoolType>> conjuncts = ExprUtils.getConjuncts(expr);
			constraints.addAll(conjuncts);
		}

		final ConstraintModel model = new ConstraintModelImpl(constDecls, constraints);

		return model;
	}

	/////////////////

	private static class ConstraintModelImpl implements ConstraintModel {
		private final Collection<ConstDecl<? extends Type>> constDecls;
		private final Collection<Expr<? extends BoolType>> constraints;

		private ConstraintModelImpl(final Collection<? extends ConstDecl<? extends Type>> constDecls,
				final Collection<? extends Expr<? extends BoolType>> constraints) {
			this.constDecls = ImmutableList.copyOf(checkNotNull(constDecls));
			this.constraints = ImmutableList.copyOf(checkNotNull(constraints));
		}

		@Override
		public Collection<ConstDecl<? extends Type>> getConstDecls() {
			return constDecls;
		}

		@Override
		public Collection<Expr<? extends BoolType>> getConstraints() {
			return constraints;
		}
	}

}
