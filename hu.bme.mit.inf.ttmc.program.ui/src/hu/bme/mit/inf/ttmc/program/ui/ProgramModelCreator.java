package hu.bme.mit.inf.ttmc.program.ui;

import hu.bme.mit.inf.ttmc.constraint.model.BasicConstraintDefinition;
import hu.bme.mit.inf.ttmc.constraint.model.ConstantDeclaration;
import hu.bme.mit.inf.ttmc.constraint.model.Expression;
import hu.bme.mit.inf.ttmc.constraint.model.Type;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.DeclTransformator;
import hu.bme.mit.inf.ttmc.constraint.ui.transform.ExprTransformator;
import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;
import hu.bme.mit.inf.ttmc.program.model.ProcedureDeclaration;
import hu.bme.mit.inf.ttmc.program.model.ProgramSpecification;
import hu.bme.mit.inf.ttmc.program.ui.impl.ProgramModelBuilder;
import hu.bme.mit.inf.ttmc.program.ui.impl.ProgramModelImpl;
import hu.bme.mit.inf.ttmc.program.ui.transform.impl.ProgramTransformationManager;

public class ProgramModelCreator {

	private ProgramModelCreator() {
	}

	public static ProgramModel create(final ProgramManager manager, final ProgramSpecification specification) {
		final ProgramTransformationManager tManager = new ProgramTransformationManager(manager);
		final ProgramModelBuilder builder = ProgramModelImpl.builder();

		addConstDecls(builder, specification, tManager);
		addConstraints(builder, specification, tManager);
		addProcDecls(builder, specification, tManager);

		return builder.build();
	}

	private static void addConstDecls(final ProgramModelBuilder builder, final ProgramSpecification specification,
			final ProgramTransformationManager manager) {

		final DeclTransformator dt = manager.getDeclTransformator();

		for (final ConstantDeclaration constantDeclaration : specification.getConstantDeclarations()) {
			@SuppressWarnings("unchecked")
			final ConstDecl<? extends Type> constDecl = (ConstDecl<? extends Type>) dt.transform(constantDeclaration);
			builder.addConstDecl(constDecl);
		}
	}

	private static void addConstraints(final ProgramModelBuilder builder, final ProgramSpecification specification,
			final ProgramTransformationManager manager) {

		final ExprTransformator et = manager.getExprTransformator();

		for (final BasicConstraintDefinition constraintDefinition : specification.getBasicConstraintDefinitions()) {
			final Expression expression = constraintDefinition.getExpression();
			final Expr<? extends BoolType> expr = ExprUtils.cast(et.transform(expression), BoolType.class);
			builder.addConstraint(expr);
		}
	}

	private static void addProcDecls(final ProgramModelBuilder builder, final ProgramSpecification specification,
			final ProgramTransformationManager manager) {

		final DeclTransformator dt = manager.getDeclTransformator();

		for (final ProcedureDeclaration procedureDeclaration : specification.getProcedureDeclarations()) {
			@SuppressWarnings("unchecked")
			final ProcDecl<? extends Type> procDecl = (ProcDecl<? extends Type>) dt.transform(procedureDeclaration);
			builder.addProcDecl(procDecl);
		}
	}
}
