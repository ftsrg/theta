package hu.bme.mit.inf.ttmc.code.visitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
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
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.AstVisitor;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.factory.StmtFactory;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.StmtFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.VarDeclFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.BlockStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public class TransformProgramVisitor implements AstVisitor<Expr<? extends Type>, Stmt, Decl<? extends Type, ?>> {

	private ExprFactory efc;
	private StmtFactory pfc;
	private TypeFactory tfc;
	private VarDeclFactory vfc;
	
	private Map<String, VarDecl<? extends Type>> symbols = new HashMap<>();
	
	public TransformProgramVisitor(ConstraintManager cm) {
		this.efc = cm.getExprFactory();
		this.tfc = cm.getTypeFactory();
		this.pfc = new StmtFactoryImpl();
		this.vfc = new VarDeclFactoryImpl(cm.getDeclFactory());
	}
	
	@Override
	public Expr<? extends Type> visit(BinaryExpressionAst ast) {
		ExpressionAst lhs = ast.getLeft();
		ExpressionAst rhs = ast.getRight();
		
		Expr<? extends Type> left  = lhs.accept(this);
		Expr<? extends Type> right = rhs.accept(this);
		
		switch (ast.getOperator()) {
			case OP_ADD:
				return this.efc.Add(ImmutableSet.of(ExprUtils.cast(left, ClosedUnderAdd.class), ExprUtils.cast(right, ClosedUnderAdd.class)));
			case OP_SUB:
				return this.efc.Sub(ExprUtils.cast(left, ClosedUnderSub.class), ExprUtils.cast(right, ClosedUnderSub.class));
			case OP_MUL:
				return this.efc.Mul(ImmutableSet.of(ExprUtils.cast(left, ClosedUnderMul.class), ExprUtils.cast(right, ClosedUnderMul.class)));
			case OP_IS_GT:
				return this.efc.Gt(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
			case OP_IS_LT:
				return this.efc.Lt(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
			case OP_IS_EQ:
				return this.efc.Eq(left, right);
			case OP_IS_NOT_EQ:
				return this.efc.Neq(left, right);
			case OP_DIV:
				return this.efc.IntDiv(ExprUtils.cast(left, IntType.class), ExprUtils.cast(right, IntType.class));
			case OP_IS_GTEQ:
				return this.efc.Geq(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
			case OP_IS_LTEQ:
				return this.efc.Leq(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
			case OP_ASSIGN: // intentional
			default:
				break;
		}
		
		return null;
	}

	@Override
	public Expr<? extends Type> visit(LiteralExpressionAst ast) {
		return this.efc.Int(ast.getValue());
	}

	@Override
	public Expr<? extends Type> visit(NameExpressionAst ast) {
		return this.symbols.get(ast.getName()).getRef();
	}

	@Override
	public Stmt visit(IfStatementAst ast) {
		ExpressionAst condAst = ast.getCondition();
		StatementAst thenAst = ast.getThen();
		StatementAst elseAst = ast.getElse();

		Expr<? extends BoolType> cond = ExprUtils.cast(condAst.accept(this), BoolType.class);
		Stmt then = thenAst.accept(this);
		
		if (elseAst != null) {
			Stmt elze = elseAst.accept(this);
			return this.pfc.If(cond, then, elze);
		} else {
			return this.pfc.If(cond, then);
		}
	}

	@Override
	public Stmt visit(CompoundStatementAst ast) {
		List<Stmt> stmts = new ArrayList<>();
		
		for (StatementAst child : ast.getStatements()) {
			stmts.add(child.accept(this));
		}
		
		return this.pfc.Block(stmts);
	}

	@Override
	public Stmt visit(VarDeclarationStatementAst ast) {
		VarDecl<?> var = this.vfc.Var(ast.getName(), this.tfc.Int());
		this.symbols.put(ast.getName(), var);
		
		return this.pfc.Decl(var);
	}

	@Override
	public Stmt visit(ReturnStatementAst ast) {
		Expr<? extends Type> expr = ast.getExpr().accept(this);
		
		return this.pfc.Return(expr);
	}

	@Override
	public Stmt visit(ExpressionStatementAst ast) {
		// Assignment hack
		ExpressionAst expr = ast.getExpression();
		
		if (expr instanceof BinaryExpressionAst && ((BinaryExpressionAst) expr).getOperator() == Operator.OP_ASSIGN) {
			BinaryExpressionAst binary = (BinaryExpressionAst) expr;
			
			Expr<? extends Type> lhs = binary.getLeft().accept(this);
			Expr<?> rhs = binary.getRight().accept(this);
			
			if (!(lhs instanceof VarRefExpr<?>)) {
				throw new RuntimeException("Assignment lvalue can only be a variable reference.");
			}
			
			VarRefExpr<Type> left = (VarRefExpr<Type>) lhs;
			
			return this.pfc.Assign(left.getDecl(), rhs);
		} else if (expr instanceof FunctionCallExpressionAst) { // Assert hack
			FunctionCallExpressionAst func = (FunctionCallExpressionAst) ast.getExpression();
			
			if (func.getName().equals("assert")) {
				ExpressionAst cond = func.getParams().get(0); // Szebben?
				return this.pfc.Assert(ExprUtils.cast(cond.accept(this), BoolType.class));
			}
		}
		
		return this.pfc.Skip();
	}

	@Override
	public Expr<? extends Type> visit(FunctionCallExpressionAst ast) {
		return null; // TODO
	}

	@Override
	public Stmt visit(WhileStatementAst ast) {
		ExpressionAst condAst = ast.getCondition();
		StatementAst  bodyAst = ast.getBody();
		
		Expr<? extends BoolType> cond = ExprUtils.cast(condAst.accept(this), BoolType.class);
		Stmt body = bodyAst.accept(this);
		
		return this.pfc.While(cond, body);
	}

	@Override
	public Stmt visit(ForStatementAst ast) {
		throw new RuntimeException("TransformProgramVisitor does not support for loops.");
	}

	@Override
	public Decl<? extends Type, ?> visit(VarDeclarationAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Decl<? extends Type, ?> visit(FunctionAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Expr<? extends Type> visit(UnaryExpressionAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Stmt visit(DoStatementAst ast) {
		ExpressionAst condAst = ast.getCondition();
		StatementAst  bodyAst = ast.getBody();
		
		Expr<? extends BoolType> cond = ExprUtils.cast(condAst.accept(this), BoolType.class);
		Stmt body = bodyAst.accept(this);
		
		return this.pfc.Do(body, cond);
	}

}
