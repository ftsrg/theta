package hu.bme.mit.inf.ttmc.code.visitor;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.code.ast.AstNode;
import hu.bme.mit.inf.ttmc.code.ast.AstVisitor;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.formalism.common.factory.ProgramFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeUtils;

public class CreateProgramAstVisitor extends AstVisitor<Expr<? extends Type>> {

	private ProgramFactory pfc;
	private TypeFactory tfc;
	private ExprFactory efc;
	private ConstraintManager cm;
	
	public CreateProgramAstVisitor(ConstraintManager cm) {
		this.cm = cm;
		this.tfc = this.cm.getTypeFactory();
		this.efc = this.cm.getExprFactory();
	}
	
	
	@Override
	public Expr<? extends Type> visit(AstNode ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expr<? extends Type> visit(NameExpressionAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expr<? extends Type> visit(LiteralExpressionAst ast) {
		return this.efc.Int(ast.getValue());
	}

	@Override
	public Expr<? extends Type> visit(BinaryExpressionAst ast) {
		ExpressionAst lhs = ast.getLeft();
		ExpressionAst rhs = ast.getRight();
		
		Expr<? extends Type> left = this.visit(lhs);
		Expr<? extends Type> right = this.visit(rhs);
		
		switch (ast.getOperator()) {
			case OP_ADD:
				
				return this.efc.Add(ImmutableSet.of(						
						ExprUtils.cast(left, ClosedUnderAdd.class), ExprUtils.cast(right, ClosedUnderAdd.class)));
		}
		
		return null;
	}

	@Override
	public Expr<? extends Type> visit(FunctionAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expr<? extends Type> visit(CompoundStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expr<? extends Type> visit(ExpressionStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

}
