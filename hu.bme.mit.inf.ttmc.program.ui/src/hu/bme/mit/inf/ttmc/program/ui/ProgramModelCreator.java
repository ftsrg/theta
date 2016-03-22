package hu.bme.mit.inf.ttmc.program.ui;

import java.util.Collection;
import java.util.HashSet;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.model.BasicConstraintDefinition;
import hu.bme.mit.inf.ttmc.constraint.model.Expression;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.ui.ExpressionHelper;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;
import hu.bme.mit.inf.ttmc.program.model.ProgramSpecification;

public class ProgramModelCreator {

	private ProgramModelCreator() {
	}

	public static ProgramModel create(final ProgramManager manager, final ProgramSpecification specification) {
		final ProgramTypeHelper typeHelper = new ProgramTypeHelper(manager.getTypeFactory());
		final ProgramDeclarationHelper declarationHelper = new ProgramDeclarationHelper(manager.getDeclFactory(),
				typeHelper);
		final ProgramExpressionHelper expressionHelper = new ProgramExpressionHelper(manager.getExprFactory(),
				declarationHelper);
		final StatementHelper statementHelper = new StatementHelper(manager.getStmtFactory(), declarationHelper,
				expressionHelper);

		final Collection<Expr<? extends BoolType>> constraints = getConstraints(expressionHelper, specification);

		return new ProgramModelImpl(constraints);
	}

	private static Collection<Expr<? extends BoolType>> getConstraints(final ExpressionHelper expressionHelper,
			final ProgramSpecification specification) {
		final Collection<Expr<? extends BoolType>> constraints = new HashSet<>();
		for (final BasicConstraintDefinition constraintDefinition : specification.getBasicConstraintDefinitions()) {
			final Expression expression = constraintDefinition.getExpression();
			final Expr<? extends BoolType> expr = ExprUtils.cast(expressionHelper.toExpr(expression), BoolType.class);
			constraints.add(expr);
		}
		return constraints;
	}

	private static final class ProgramModelImpl implements ProgramModel {

		final Collection<Expr<? extends BoolType>> constraints;

		private ProgramModelImpl(final Collection<Expr<? extends BoolType>> constraints) {
			this.constraints = ImmutableSet.copyOf(constraints);
		}

		@Override
		public Collection<ConstDecl<? extends Type>> getConstDecls() {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public Collection<Expr<? extends BoolType>> getConstraints() {
			return constraints;
		}

		@Override
		public Collection<ProcDecl<? extends Type>> getProcDecls() {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public ProcedureModel getProcedureModel(final ProcDecl<? extends Type> procDecl) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}
	}

}
