package hu.bme.mit.inf.ttmc.code;

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
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTEqualsInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTExpressionList;

import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.ast.AssignmentInitializerAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationSpecifierAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionListAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;

public class AstTransformer {
		
	public static TranslationUnitAst transform(IASTTranslationUnit ast) {
		List<DeclarationAst> functions = new ArrayList<>();
		
		for (IASTNode child : ast.getChildren()) {
			if (child instanceof IASTFunctionDefinition) {
				functions.add(transformFunction((IASTFunctionDefinition) child));
			}
		}
						
		return new TranslationUnitAst(functions);
	}
	
	public static FunctionDefinitionAst transformFunction(IASTFunctionDefinition ast) {
		IASTFunctionDeclarator decl = ast.getDeclarator();
		String name = decl.getName().toString();
		
		FunctionDeclaratorAst funcDeclarator = new FunctionDeclaratorAst(name);
		
		CompoundStatementAst body = transformCompoundStatement((IASTCompoundStatement)ast.getBody());
		
		DeclarationSpecifierAst spec = transformDeclSpecifier(ast.getDeclSpecifier());
		
		return new FunctionDefinitionAst(name, spec, funcDeclarator, body);
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
		
		if (decl instanceof IASTSimpleDeclaration) {
			IASTSimpleDeclaration varDecl = (IASTSimpleDeclaration) decl;
			IASTDeclSpecifier spec = varDecl.getDeclSpecifier();
			
			DeclarationSpecifierAst declSpec = transformDeclSpecifier(spec);
			
			List<DeclaratorAst> declarators = new ArrayList<>();
			for (IASTDeclarator declarator : varDecl.getDeclarators()) {
				String name = declarator.getName().toString();
				IASTInitializer init = declarator.getInitializer();
				
				if (init == null) {
					InitDeclaratorAst declAst = new InitDeclaratorAst(name);					
					declarators.add(declAst);
				} else if (init instanceof IASTEqualsInitializer) {
					IASTInitializerClause clause = ((IASTEqualsInitializer) init).getInitializerClause();
					if (clause instanceof IASTExpression) {
						IASTExpression exprAst = (IASTExpression) clause;
						
						InitDeclaratorAst declAst = new InitDeclaratorAst(name, new AssignmentInitializerAst(transformExpression(exprAst)));				
						declarators.add(declAst);
					} else {
						throw new UnsupportedOperationException("Only assignment initializators are supported");
					}
				} else {
					throw new UnsupportedOperationException();
				}				
			}
			
			return new DeclarationStatementAst(new VarDeclarationAst(declSpec, declarators));
		}
		
		return null;
	}
	
	private static DeclarationSpecifierAst transformDeclSpecifier(IASTDeclSpecifier spec) {
		EnumSet<DeclarationSpecifierAst.StorageClassSpecifier> storage = EnumSet.noneOf(DeclarationSpecifierAst.StorageClassSpecifier.class);
		EnumSet<DeclarationSpecifierAst.TypeQualifier> type = EnumSet.noneOf(DeclarationSpecifierAst.TypeQualifier.class);
		EnumSet<DeclarationSpecifierAst.FunctionSpecifier> func = EnumSet.noneOf(DeclarationSpecifierAst.FunctionSpecifier.class);
		
		int sc = spec.getStorageClass();
		
		if ((sc & spec.sc_typedef) != 0) {
			storage.add(DeclarationSpecifierAst.StorageClassSpecifier.TYPEDEF);
		}
		
		if ((sc & spec.sc_extern) != 0) {
			storage.add(DeclarationSpecifierAst.StorageClassSpecifier.EXTERN);
		}
		
		if ((sc & spec.sc_static) != 0) {
			storage.add(DeclarationSpecifierAst.StorageClassSpecifier.STATIC);
		}
		
		if ((sc & spec.sc_auto) != 0) {
			storage.add(DeclarationSpecifierAst.StorageClassSpecifier.AUTO);
		}
		
		if ((sc & spec.sc_register) != 0) {
			storage.add(DeclarationSpecifierAst.StorageClassSpecifier.REGISTER);
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
			func.add(DeclarationSpecifierAst.FunctionSpecifier.INLINE);
		}
		
		return new DeclarationSpecifierAst(storage, type, func);
	}

	private static InitDeclaratorAst transformDeclarator(IASTDeclarator ast) {
		String name = ast.getName().toString();
		
		return new InitDeclaratorAst(name);
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
		
		return null; // @todo
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
				return new UnaryExpressionAst(transformExpression(expr), Operator.OP_PREFIX_INCR);
			case IASTUnaryExpression.op_postFixDecr:
				return new UnaryExpressionAst(transformExpression(expr), Operator.OP_PREFIX_INCR);
			case IASTUnaryExpression.op_not:
				return new UnaryExpressionAst(transformExpression(expr), Operator.OP_NOT);
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
		}
		
		return null;
	}
	
}
