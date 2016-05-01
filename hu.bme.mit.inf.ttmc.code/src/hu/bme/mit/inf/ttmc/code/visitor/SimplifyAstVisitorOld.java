package hu.bme.mit.inf.ttmc.code.visitor;

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;

import hu.bme.mit.inf.ttmc.code.ast.AstNode;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.AstVisitor;

public class SimplifyAstVisitorOld implements AstVisitor<ExpressionAst, StatementAst, DeclarationAst, DeclaratorAst> {

	private Map<String, DeclarationAst> names = new HashMap<>();
	private Stack<List<String>> scopes = new Stack<>();
	private Map<String, String> scopeMappings = new HashMap<>();
	
	private int uniqid = 0;
	
	public SimplifyAstVisitorOld() {
	}
	
	@Override
	public ExpressionAst visit(BinaryExpressionAst ast) {
        return new BinaryExpressionAst(ast.getLeft().accept(this), ast.getRight().accept(this), ast.getOperator());
	}

	@Override
	public ExpressionAst visit(LiteralExpressionAst ast) {
		return new LiteralExpressionAst(ast.getValue());
	}
	
	@Override
	public ExpressionAst visit(NameExpressionAst ast) {		
		return new NameExpressionAst(this.scopeMappings.containsKey(ast.getName()) ? this.scopeMappings.get(ast.getName()) : ast.getName());
	}

	@Override
	public ExpressionAst visit(FunctionCallExpressionAst ast) {
		List<ExpressionAst> args = new ArrayList<>();
		
		for (ExpressionAst expr : ast.getParams()) {
			args.add(expr.accept(this));
		}
		
		return new FunctionCallExpressionAst(ast.getName(), args);
	}

	@Override
	public StatementAst visit(IfStatementAst ast) {
		ExpressionAst cond = this.resolveConditions(ast.getCondition().accept(this));
				
		if (ast.getElse() != null) {
			return new IfStatementAst(cond, ast.getThen().accept(this), ast.getElse().accept(this));
		} else {
			return new IfStatementAst(cond, ast.getThen().accept(this));
		}
	}

	@Override
	public StatementAst visit(CompoundStatementAst ast) {
		// Enter scope
		this.enterScope();
		
		List<StatementAst> stmts = new ArrayList<>();
		
		for (StatementAst stmt : ast.getStatements()) {
			stmts.add(stmt.accept(this));
		}
				
		this.leaveScope();
		
		return new CompoundStatementAst(stmts);
	}

	@Override
	public StatementAst visit(DeclarationStatementAst ast) {		
		return new DeclarationStatementAst(ast.getDeclaration().accept(this));
	}

	@Override
	public StatementAst visit(ReturnStatementAst ast) {
		return new ReturnStatementAst(ast.getExpression().accept(this));
	}

	@Override
	public StatementAst visit(ExpressionStatementAst ast) {
		ExpressionAst expr = ast.getExpression().accept(this);
		return new ExpressionStatementAst(expr);
	}

	@Override
	public StatementAst visit(WhileStatementAst ast) {
		return new WhileStatementAst(this.resolveConditions(ast.getCondition().accept(this)), ast.getBody().accept(this));
	}

	@Override
	public StatementAst visit(ForStatementAst ast) {
		// Resolve for statements into whiles
		StatementAst  init = ast.getInit().accept(this);
		ExpressionAst cond = this.resolveConditions(ast.getCondition().accept(this));
		ExpressionAst iter = ast.getIteration().accept(this);
		StatementAst body  = ast.getBody().accept(this);
		
		StatementAst newBody;
		
		if (body instanceof CompoundStatementAst) {
			((CompoundStatementAst) body).getStatements().add(new ExpressionStatementAst(iter));
			newBody = body;
		} else {
			List<StatementAst> whileBody = new ArrayList<>();
			whileBody.add(body);
			whileBody.add(new ExpressionStatementAst(iter));
			newBody = new CompoundStatementAst(whileBody);
		}
				
		List<StatementAst> stmts = new ArrayList<>();
		stmts.add(init);
		stmts.add(new WhileStatementAst(cond, newBody));
		
		return new CompoundStatementAst(stmts);
	}
	
	IASTDeclSpecifier decl;

	@Override
	public DeclarationAst visit(VarDeclarationAst ast) {
		List<DeclaratorAst> newDeclarators = new ArrayList<>();
		List<DeclaratorAst> declarators = ast.getDeclarators();
		for (DeclaratorAst declarator : declarators) {
			String name = declarator.getName();
			if (this.hasInScope(name)) {
				String newName = name + "_conflict" + uniqid++;
				this.scopeMappings.put(name, newName);
				newDeclarators.add(new InitDeclaratorAst(newName));
				this.scopes.lastElement().add(newName);
			} else {
				newDeclarators.add(new InitDeclaratorAst(name));
				this.scopes.lastElement().add(name);
			}
		}
		
		return new VarDeclarationAst(ast.getSpecifier(), newDeclarators);
	}

	@Override
	public DeclarationAst visit(FunctionDefinitionAst ast) {
		return new FunctionDefinitionAst(ast.getName(), ast.getDeclarationSpecifier(), ast.getDeclarator(), (CompoundStatementAst) ast.getBody().accept(this));
	}
/*
	@Override
	public DeclaratorAst visit(InitDeclaratorAst ast) {
		return new InitDeclaratorAst(ast.getName());
	}
	
	public DeclaratorAst visit(FunctionDeclaratorAst ast) {
		return new FunctionDeclaratorAst(ast.getName());
	}
*/
	@Override
	public ExpressionAst visit(UnaryExpressionAst ast) {
		ExpressionAst operand = ast.getOperand().accept(this);
				
		return new UnaryExpressionAst(operand, ast.getOperator());
	}

	@Override
	public StatementAst visit(DoStatementAst ast) {
		return new DoStatementAst(ast.getCondition().accept(this), ast.getBody().accept(this));
	}

	private ExpressionAst resolveConditions(ExpressionAst ast) {
		if (ast instanceof LiteralExpressionAst) {
			return new BinaryExpressionAst(ast, new LiteralExpressionAst(0), Operator.OP_IS_NOT_EQ);
		}
		
		return ast;
	}

	private void leaveScope() {
		this.scopes.pop();
		this.scopeMappings.clear();		
	}

	private void enterScope() {
		this.scopes.add(new ArrayList<String>());
	}
	
	private boolean hasInScope(String name) {
		for (List<String> list : this.scopes) {
			if (list.contains(name))
				return true;
		}
		
		return false;
	}

	@Override
	public DeclaratorAst visit(InitDeclaratorAst ast) {
		return new InitDeclaratorAst(ast.getName());
	}

	@Override
	public DeclaratorAst visit(FunctionDeclaratorAst ast) {
		return new FunctionDeclaratorAst(ast.getName());
	}

	@Override
	public StatementAst visit(SwitchStatementAst ast) {
		return new SwitchStatementAst(ast.getExpression().accept(this), ast.getBody().accept(this));
	}

	@Override
	public StatementAst visit(CaseStatementAst ast) {
		return new CaseStatementAst(ast.getExpression().accept(this));
	}

	@Override
	public StatementAst visit(DefaultStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(ContinueStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(BreakStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(GotoStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(LabeledStatementAst ast) {
		return ast;
	}

	@Override
	public StatementAst visit(NullStatementAst ast) {
		return ast;
	}
}
