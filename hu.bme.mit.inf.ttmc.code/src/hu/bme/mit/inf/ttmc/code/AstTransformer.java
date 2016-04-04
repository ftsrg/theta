package hu.bme.mit.inf.ttmc.code;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTEqualsInitializer;

import hu.bme.mit.inf.ttmc.code.ast.AstRoot;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;

public class AstTransformer {

	public static AstRoot transform(IASTTranslationUnit ast) {
		List<FunctionAst> functions = new ArrayList<>();
		
		for (IASTNode child : ast.getChildren()) {
			if (child instanceof IASTFunctionDefinition) {
				functions.add(transformFunction((IASTFunctionDefinition) child));
			}
		}
		
		return new AstRoot(functions);
	}
	
	public static FunctionAst transformFunction(IASTFunctionDefinition ast) {
		IASTFunctionDeclarator decl = ast.getDeclarator();
		String name = decl.getName().toString();
		
		CompoundStatementAst body = transformCompoundStatement((IASTCompoundStatement)ast.getBody());
		
		return new FunctionAst(name, body);
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
		
		return null;		
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
		StatementAst elseStmt = transformStatement(ast.getElseClause());
				
		return new IfStatementAst(cond, thenStmt, elseStmt);
	}
	
	private static VarDeclarationStatementAst transformDeclarationStatement(IASTDeclarationStatement ast) {
		IASTDeclaration decl = ast.getDeclaration();
		
		if (decl instanceof IASTSimpleDeclaration) {
			IASTSimpleDeclaration varDecl = (IASTSimpleDeclaration) decl;
			String name = varDecl.getDeclarators()[0].getName().toString();
			
			return new VarDeclarationStatementAst(new VarDeclarationAst(name));
		}
		
		return null;
	}
	
	private static DeclaratorAst transformDeclarator(IASTDeclarator ast) {
		String name = ast.getName().toString();
		IASTInitializer init = ast.getInitializer();
		
		if (init == null) {
			return new DeclaratorAst();
		}
		
		if (init instanceof IASTEqualsInitializer) {
			IASTInitializerClause clause = ((IASTEqualsInitializer) init).getInitializerClause();
			if (clause instanceof IASTExpression) {
				ExpressionAst expr = transformExpression((IASTExpression) clause);
			}
		}
		
		throw new UnsupportedOperationException();
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
		
		return null; // @todo
	}
	
	private static UnaryExpressionAst transformUnaryExpression(IASTUnaryExpression ast) {
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
		}
		
		return null;		
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
