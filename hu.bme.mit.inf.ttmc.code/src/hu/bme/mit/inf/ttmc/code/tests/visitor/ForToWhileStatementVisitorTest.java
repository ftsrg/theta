package hu.bme.mit.inf.ttmc.code.tests.visitor;

import static org.junit.Assert.*;

import java.util.ArrayList;

import org.junit.Test;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.code.ast.AssignmentInitializerAst;
import hu.bme.mit.inf.ttmc.code.ast.AstNode;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationSpecifierAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.ExpressionVisitor;
import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;
import hu.bme.mit.inf.ttmc.code.visitor.ForToWhileStatementVisitor;

public class ForToWhileStatementVisitorTest {
	
	@Test
	public void testWithCompoundStatement() {	
		StatementAst init = new DeclarationStatementAst(new VarDeclarationAst(new DeclarationSpecifierAst(),
			new ArrayList<DeclaratorAst>() {{
				add(new InitDeclaratorAst("x", new AssignmentInitializerAst(new LiteralExpressionAst(0))));	
			}}
		));
		
		BinaryExpressionAst cond = new BinaryExpressionAst(
			new NameExpressionAst("i"), new LiteralExpressionAst(5), Operator.OP_IS_LT
		);
		BinaryExpressionAst iter = new BinaryExpressionAst(
			new NameExpressionAst("i") ,
			new BinaryExpressionAst(
				new NameExpressionAst("i"),
				new LiteralExpressionAst(1),
				Operator.OP_ADD
			),
			Operator.OP_ASSIGN
		);
		
		StatementAst body = new CompoundStatementAst(
			new ArrayList<StatementAst>() {{
				add(new ExpressionStatementAst(new UnaryExpressionAst(new NameExpressionAst("x"), UnaryExpressionAst.Operator.OP_PREFIX_INCR)));
			}}
		);
		
		// for (int i = 0; i < 5; i = i + 1) { x++; }
		ForStatementAst forStmt = new ForStatementAst(init, cond, iter, body);
		
		ForToWhileStatementVisitor visitor = new ForToWhileStatementVisitor();
		
		StatementAst result = forStmt.accept(visitor);
		
		assertTrue(result instanceof CompoundStatementAst);
		
		CompoundStatementAst top = (CompoundStatementAst) result;		
		
		assertEquals(init, top.getStatements().get(0));		
		
		assertTrue(top.getStatements().get(1) instanceof WhileStatementAst);
		
		WhileStatementAst whileStmt = (WhileStatementAst) top.getStatements().get(1);
		assertEquals(cond, whileStmt.getCondition());
		assertTrue(whileStmt.getBody() instanceof CompoundStatementAst);
		
		CompoundStatementAst whileBody = (CompoundStatementAst) whileStmt.getBody();
		
		//assertEquals(iter, whileBody.getStatements().get(whileBody.getStatements().size() - 1));		
	}

}
