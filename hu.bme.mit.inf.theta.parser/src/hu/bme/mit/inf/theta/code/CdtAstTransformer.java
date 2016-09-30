package hu.bme.mit.inf.theta.code;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTContinueStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;

import hu.bme.mit.inf.theta.code.ast.AssignmentInitializerAst;
import hu.bme.mit.inf.theta.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.theta.code.ast.BreakStatementAst;
import hu.bme.mit.inf.theta.code.ast.CaseStatementAst;
import hu.bme.mit.inf.theta.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.theta.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.theta.code.ast.DeclarationAst;
import hu.bme.mit.inf.theta.code.ast.DeclarationSpecifierAst;
import hu.bme.mit.inf.theta.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.theta.code.ast.DeclaratorAst;
import hu.bme.mit.inf.theta.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.theta.code.ast.DoStatementAst;
import hu.bme.mit.inf.theta.code.ast.ExpressionAst;
import hu.bme.mit.inf.theta.code.ast.ExpressionListAst;
import hu.bme.mit.inf.theta.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.theta.code.ast.ForStatementAst;
import hu.bme.mit.inf.theta.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.theta.code.ast.FunctionDeclaratorAst;
import hu.bme.mit.inf.theta.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.theta.code.ast.GotoStatementAst;
import hu.bme.mit.inf.theta.code.ast.IfStatementAst;
import hu.bme.mit.inf.theta.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.theta.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.theta.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.theta.code.ast.NameExpressionAst;
import hu.bme.mit.inf.theta.code.ast.NullStatementAst;
import hu.bme.mit.inf.theta.code.ast.ParameterDeclarationAst;
import hu.bme.mit.inf.theta.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.theta.code.ast.StatementAst;
import hu.bme.mit.inf.theta.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.theta.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.theta.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.theta.code.ast.UnaryExpressionAst.Operator;
import hu.bme.mit.inf.theta.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.theta.code.ast.WhileStatementAst;

public class CdtAstTransformer {

	public static TranslationUnitAst transform(IASTTranslationUnit ast) {
		List<DeclarationAst> functions = new ArrayList<>();

		for (IASTDeclaration child : ast.getDeclarations()) {
			functions.add(transformDeclaration(child));
		}

		return new TranslationUnitAst(functions);
	}

	public static DeclarationAst transformDeclaration(IASTDeclaration ast) {
		if (ast instanceof IASTSimpleDeclaration) {
			IASTSimpleDeclaration varDecl = (IASTSimpleDeclaration) ast;
			IASTDeclSpecifier spec = varDecl.getDeclSpecifier();

			DeclarationSpecifierAst declSpec = transformDeclSpecifier(spec);

			List<DeclaratorAst> declarators = new ArrayList<>();
			for (IASTDeclarator declarator : varDecl.getDeclarators()) {
				DeclaratorAst declaratorRes = transformDeclarator(declarator);
				declarators.add(declaratorRes);
			}

			return new VarDeclarationAst(declSpec, declarators);
		} else if (ast instanceof IASTFunctionDefinition) {
			return transformFunctionDefinition((IASTFunctionDefinition) ast);
		} else {
			throw new UnsupportedOperationException("Unsupported declaration type: " + ast.getClass());
		}

	}

	public static FunctionDefinitionAst transformFunctionDefinition(IASTFunctionDefinition ast) {
		IASTFunctionDeclarator decl = ast.getDeclarator();
		String name = decl.getName().toString();

		FunctionDeclaratorAst funcDeclarator = transformFunctionDeclarator(decl);
		CompoundStatementAst body = transformCompoundStatement((IASTCompoundStatement)ast.getBody());
		DeclarationSpecifierAst spec = transformDeclSpecifier(ast.getDeclSpecifier());

		return new FunctionDefinitionAst(name, spec, funcDeclarator, body);
	}

	private static FunctionDeclaratorAst transformFunctionDeclarator(IASTFunctionDeclarator ast) {
		String name = ast.getName().toString();
		List<ParameterDeclarationAst> params = new ArrayList<>();

		if (ast instanceof IASTStandardFunctionDeclarator) {
			IASTParameterDeclaration[] paramDecls = ((IASTStandardFunctionDeclarator) ast).getParameters();
			for (IASTParameterDeclaration pd : paramDecls) {
				params.add(new ParameterDeclarationAst(transformDeclSpecifier(pd.getDeclSpecifier()), transformDeclarator(pd.getDeclarator())));
			}
		} else {
			throw new UnsupportedOperationException("Unsupported function declarator");
		}

		return new FunctionDeclaratorAst(name, params);
	}

	private static StatementAst transformStatement(IASTStatement ast) {
		if (ast instanceof IASTCompoundStatement) {
			return transformCompoundStatement((IASTCompoundStatement) ast);
		}

		if (ast instanceof IASTDeclarationStatement) {
			return transformDeclarationStatement((IASTDeclarationStatement) ast);
		}

		if (ast instanceof IASTExpressionStatement) {
			return transformExpressionStatement((IASTExpressionStatement) ast);
		}

		if (ast instanceof IASTReturnStatement) {
			return transformReturnStatement((IASTReturnStatement) ast);
		}

		if (ast instanceof IASTIfStatement) {
			return transformIfStatement((IASTIfStatement) ast);
		}

		if (ast instanceof IASTWhileStatement) {
			return transformWhileStatement((IASTWhileStatement) ast);
		}

		if (ast instanceof IASTForStatement) {
			return transformForStatement((IASTForStatement) ast);
		}

		if (ast instanceof IASTDoStatement) {
			return transformDoStatement((IASTDoStatement) ast);
		}

		if (ast instanceof IASTSwitchStatement) {
			return transformSwitchStatement((IASTSwitchStatement) ast);
		}

		if (ast instanceof IASTCaseStatement) {
			IASTCaseStatement caseAst = (IASTCaseStatement) ast;
			return new CaseStatementAst(transformExpression(caseAst.getExpression()));
		}

		if (ast instanceof IASTLabelStatement) {
			IASTLabelStatement labelStmt = (IASTLabelStatement) ast;
			String label = labelStmt.getName().toString();

			return new LabeledStatementAst(label, transformStatement(labelStmt.getNestedStatement()));
		}

		if (ast instanceof IASTDefaultStatement) {
			return new DefaultStatementAst();
		}

		if (ast instanceof IASTContinueStatement) {
			return new ContinueStatementAst();
		}

		if (ast instanceof IASTBreakStatement) {
			return new BreakStatementAst();
		}

		if (ast instanceof IASTNullStatement) {
			return new NullStatementAst();
		}

		if (ast instanceof IASTGotoStatement) {
			return new GotoStatementAst(((IASTGotoStatement) ast).getName().toString());
		}

		throw new UnsupportedOperationException("Statement class " + ast.getClass().getName() + " is not supported.");
	}

	private static SwitchStatementAst transformSwitchStatement(IASTSwitchStatement ast) {
		ExpressionAst expr = transformExpression(ast.getControllerExpression());
		StatementAst  body = transformStatement(ast.getBody());

		return new SwitchStatementAst(expr, body);
	}

	private static StatementAst transformDoStatement(IASTDoStatement ast) {
		ExpressionAst cond = transformExpression(ast.getCondition());
		StatementAst body = transformStatement(ast.getBody());

		return new DoStatementAst(cond, body);
	}

	private static ForStatementAst transformForStatement(IASTForStatement ast) {
		StatementAst init = transformStatement(ast.getInitializerStatement());
		ExpressionAst cond = transformExpression(ast.getConditionExpression());
		ExpressionAst iter = transformExpression(ast.getIterationExpression());
		StatementAst body = transformStatement(ast.getBody());

		return new ForStatementAst(init, cond, iter, body);
	}

	private static StatementAst transformWhileStatement(IASTWhileStatement ast) {
		ExpressionAst cond = transformExpression(ast.getCondition());
		StatementAst body  = transformStatement(ast.getBody());

		return new WhileStatementAst(cond, body);
	}

	private static IfStatementAst transformIfStatement(IASTIfStatement ast) {
		ExpressionAst cond = transformExpression(ast.getConditionExpression());
		StatementAst thenStmt = transformStatement(ast.getThenClause());
		StatementAst elseStmt = ast.getElseClause() != null ? transformStatement(ast.getElseClause()) : null;

		return new IfStatementAst(cond, thenStmt, elseStmt);
	}

	private static DeclarationStatementAst transformDeclarationStatement(IASTDeclarationStatement ast) {
		IASTDeclaration decl = ast.getDeclaration();

		DeclarationAst declaration = transformDeclaration(decl);

		return new DeclarationStatementAst(declaration);
	}

	private static DeclarationSpecifierAst transformDeclSpecifier(IASTDeclSpecifier spec) {
		DeclarationSpecifierAst.StorageClassSpecifier storage = DeclarationSpecifierAst.StorageClassSpecifier.NONE;
		EnumSet<DeclarationSpecifierAst.TypeQualifier> type = EnumSet.noneOf(DeclarationSpecifierAst.TypeQualifier.class);
		DeclarationSpecifierAst.FunctionSpecifier func = DeclarationSpecifierAst.FunctionSpecifier.NONE;

		int sc = spec.getStorageClass();

		if (sc == IASTDeclSpecifier.sc_typedef) {
			storage = DeclarationSpecifierAst.StorageClassSpecifier.TYPEDEF;
		} else if (sc == IASTDeclSpecifier.sc_extern) {
			storage = DeclarationSpecifierAst.StorageClassSpecifier.EXTERN;
		} else if (sc == IASTDeclSpecifier.sc_static) {
			storage = DeclarationSpecifierAst.StorageClassSpecifier.STATIC;
		} else if (sc == IASTDeclSpecifier.sc_auto) {
			storage = DeclarationSpecifierAst.StorageClassSpecifier.AUTO;
		} else if (sc == IASTDeclSpecifier.sc_register) {
			storage = DeclarationSpecifierAst.StorageClassSpecifier.REGISTER;
		}

		if (spec.isConst()) {
			type.add(DeclarationSpecifierAst.TypeQualifier.CONST);
		}

		if (spec.isVolatile()) {
			type.add(DeclarationSpecifierAst.TypeQualifier.VOLATILE);
		}

		if (spec.isRestrict()) {
			type.add(DeclarationSpecifierAst.TypeQualifier.RESTRICT);
		}

		if (spec.isInline()) {
			func = DeclarationSpecifierAst.FunctionSpecifier.INLINE;
		}

		return new DeclarationSpecifierAst(storage, type, func);
	}

	private static DeclaratorAst transformDeclarator(IASTDeclarator ast) {
		if (ast instanceof IASTFunctionDeclarator) {
			return transformFunctionDeclarator((IASTFunctionDeclarator) ast);
		} else {
			String name = ast.getName().toString();
			IASTInitializer init = ast.getInitializer();

			if (init == null) {
				return new InitDeclaratorAst(name);
			} else if (init instanceof IASTEqualsInitializer) {
				IASTInitializerClause clause = ((IASTEqualsInitializer) init).getInitializerClause();
				if (clause instanceof IASTExpression) {
					IASTExpression exprAst = (IASTExpression) clause;

					return new InitDeclaratorAst(name, new AssignmentInitializerAst(transformExpression(exprAst)));
				} else {
					throw new UnsupportedOperationException("Only assignment initializators are supported");
				}
			} else {
				throw new UnsupportedOperationException("Unsupported initializer: " + init.getClass().getName());
			}
		}
	}

	private static ExpressionStatementAst transformExpressionStatement(IASTExpressionStatement ast) {
		ExpressionAst expr = transformExpression(ast.getExpression());

		return new ExpressionStatementAst(expr);
	}

	private static ReturnStatementAst transformReturnStatement(IASTReturnStatement ast) {
		ExpressionAst expr = transformExpression(ast.getReturnValue());

		return new ReturnStatementAst(expr);
	}

	private static CompoundStatementAst transformCompoundStatement(IASTCompoundStatement ast) {
		List<StatementAst> statements = new ArrayList<>();

		for (IASTStatement stmt : ast.getStatements()) {
			statements.add(transformStatement(stmt));
		}

		return new CompoundStatementAst(statements);
	}

	public static ExpressionAst transformExpression(IASTExpression ast) {
		if (ast instanceof IASTBinaryExpression) {
			return transformBinaryExpression((IASTBinaryExpression)ast);
		}

		if (ast instanceof IASTLiteralExpression) {
			return transformLiteral((IASTLiteralExpression) ast);
		}

		if (ast instanceof IASTIdExpression) {
			return transformNameExpression((IASTIdExpression) ast);
		}

		if (ast instanceof IASTFunctionCallExpression) {
			return transformFunctionCallExpression((IASTFunctionCallExpression) ast);
		}

		if (ast instanceof IASTUnaryExpression) {
			return transformUnaryExpression((IASTUnaryExpression) ast);
		}

		if (ast instanceof IASTExpressionList) {
			return transformExpressionList((IASTExpressionList) ast);
		}

		throw new UnsupportedOperationException("Unsupported expression type " + ast.getClass());
	}

	private static ExpressionListAst transformExpressionList(IASTExpressionList ast) {
		List<ExpressionAst> newExpressions = new ArrayList<>();
		for (IASTExpression expr : ast.getExpressions()) {
			newExpressions.add(transformExpression(expr));
		}

		return new ExpressionListAst(newExpressions);
	}

	private static ExpressionAst transformUnaryExpression(IASTUnaryExpression ast) {
		IASTExpression expr = ast.getOperand();

		switch (ast.getOperator()) {
			case IASTUnaryExpression.op_prefixIncr:
				return new UnaryExpressionAst(transformExpression(expr), Operator.OP_PREFIX_INCR);
			case IASTUnaryExpression.op_postFixIncr:
				return new UnaryExpressionAst(transformExpression(expr), Operator.OP_POSTFIX_INCR);
			case IASTUnaryExpression.op_prefixDecr:
				return new UnaryExpressionAst(transformExpression(expr), Operator.OP_PREFIX_DECR);
			case IASTUnaryExpression.op_postFixDecr:
				return new UnaryExpressionAst(transformExpression(expr), Operator.OP_POSTFIX_DECR);
			case IASTUnaryExpression.op_not:
				return new UnaryExpressionAst(transformExpression(expr), Operator.OP_NOT);
			case IASTUnaryExpression.op_minus:
				return new UnaryExpressionAst(transformExpression(expr), Operator.OP_MINUS);
			case IASTUnaryExpression.op_bracketedPrimary:
				return transformExpression(expr);
		}

		throw new UnsupportedOperationException("Operator " + ast.getOperator() + " is not supported");
	}

	private static FunctionCallExpressionAst transformFunctionCallExpression(IASTFunctionCallExpression ast) {
		IASTExpression functionName = ast.getFunctionNameExpression();
		if (functionName instanceof IASTIdExpression) {
			String name = ((IASTIdExpression) functionName).getName().toString();

			List<ExpressionAst> args = new ArrayList<>();
			for (IASTInitializerClause arg : ast.getArguments()) {
				IASTExpression expr = (IASTExpression) arg;
				args.add(transformExpression(expr));
			}

			return new FunctionCallExpressionAst(name, args);
		}

		return null;
	}

	public static NameExpressionAst transformNameExpression(IASTIdExpression ast) {
		String name = ast.getName().toString();
		return new NameExpressionAst(name);
	}

	public static LiteralExpressionAst transformLiteral(IASTLiteralExpression ast) {
		String value = new String(ast.getValue()).toUpperCase();
		if (value.endsWith("L")) { // TODO: Hack
			return new LiteralExpressionAst((int) Long.parseLong(value.replace("L", "")));
		}

		return new LiteralExpressionAst(Integer.parseInt(new String(ast.getValue())));
	}

	public static BinaryExpressionAst transformBinaryExpression(IASTBinaryExpression ast) {
		ExpressionAst left = transformExpression(ast.getOperand1());
		ExpressionAst right = transformExpression(ast.getOperand2());

		switch (ast.getOperator()) {
		case IASTBinaryExpression.op_plus:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_ADD);
		case IASTBinaryExpression.op_minus:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_SUB);
		case IASTBinaryExpression.op_multiply:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_MUL);
		case IASTBinaryExpression.op_divide:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_DIV);
		case IASTBinaryExpression.op_modulo:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_MOD);
		case IASTBinaryExpression.op_assign:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_ASSIGN);
		case IASTBinaryExpression.op_greaterThan:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_GT);
		case IASTBinaryExpression.op_equals:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_EQ);
		case IASTBinaryExpression.op_notequals:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_NOT_EQ);
		case IASTBinaryExpression.op_lessThan:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_LT);
		case IASTBinaryExpression.op_greaterEqual:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_GTEQ);
		case IASTBinaryExpression.op_lessEqual:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_LTEQ);
		case IASTBinaryExpression.op_plusAssign:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_ADD_ASSIGN);
		case IASTBinaryExpression.op_minusAssign:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_SUB_ASSIGN);
		case IASTBinaryExpression.op_multiplyAssign:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_MUL_ASSIGN);
		case IASTBinaryExpression.op_divideAssign:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_DIV_ASSIGN);
		case IASTBinaryExpression.op_moduloAssign:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_MOD_ASSIGN);
		case IASTBinaryExpression.op_logicalAnd:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_LOGIC_AND);
		case IASTBinaryExpression.op_logicalOr:
			return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_LOGIC_OR);
		}

		throw new ParserException("Unknown binary operator.");
	}

}
