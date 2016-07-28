package hu.bme.mit.inf.ttmc.code.visitor;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Gt;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.IntDiv;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Mod;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Mul;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neg;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Sub;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.code.TransformException;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionListAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclarationVisitor;
import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclaratorVisitor;
import hu.bme.mit.inf.ttmc.code.ast.visitor.ExpressionVisitor;
import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;
import hu.bme.mit.inf.ttmc.code.ast.visitor.TranslationUnitVisitor;
import hu.bme.mit.inf.ttmc.code.util.SymbolTable;
import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.GlobalContext;

import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.*;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.*;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.*;

public class TransformProgramVisitor implements
	ExpressionVisitor<Expr<? extends Type>>,
	StatementVisitor<BasicBlock>,
	DeclarationVisitor<Decl<? extends Type, ?>>,
	DeclaratorVisitor<Decl<? extends Type, ?>>,
	TranslationUnitVisitor<GlobalContext>
{

	private SymbolTable<Decl<? extends Type, ?>> symbols = new SymbolTable<>();
	private Map<ProcDecl<? extends Type>, Function> functionTable = new HashMap<>();

	@Override
	public Expr<? extends Type> visit(BinaryExpressionAst ast) {
		ExpressionAst lhs = ast.getLeft();
		ExpressionAst rhs = ast.getRight();

		Expr<? extends Type> left  = lhs.accept(this);
		Expr<? extends Type> right = rhs.accept(this);

		switch (ast.getOperator()) {
			case OP_ADD:
				return Add(ExprUtils.cast(left, ClosedUnderAdd.class), ExprUtils.cast(right, ClosedUnderAdd.class));
			case OP_SUB:
				return Sub(ExprUtils.cast(left, ClosedUnderSub.class), ExprUtils.cast(right, ClosedUnderSub.class));
			case OP_MUL:
				return Mul(ExprUtils.cast(left, ClosedUnderMul.class), ExprUtils.cast(right, ClosedUnderMul.class));
			case OP_DIV:
				return IntDiv(ExprUtils.cast(left, IntType.class), ExprUtils.cast(right, IntType.class));
			case OP_MOD:
				return Mod(ExprUtils.cast(left, IntType.class), ExprUtils.cast(right, IntType.class));
			case OP_IS_GT:
				return Gt(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
			case OP_IS_LT:
				return Lt(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
			case OP_IS_EQ:
				return Eq(left, right);
			case OP_IS_NOT_EQ:
				return Neq(left, right);
			case OP_IS_GTEQ:
				return Geq(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
			case OP_IS_LTEQ:
				return Leq(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
			case OP_LOGIC_AND:
				return And(ExprUtils.cast(left, BoolType.class), ExprUtils.cast(right, BoolType.class));
			case OP_LOGIC_OR:
				return Or(ExprUtils.cast(left, BoolType.class), ExprUtils.cast(right, BoolType.class));
			case OP_ASSIGN: // intentional
			default:
				throw new UnsupportedOperationException("This code should not be reachable.");
		}
	}

	@Override
	public Expr<? extends Type> visit(UnaryExpressionAst ast) {
		switch (ast.getOperator()) {
		case OP_MINUS:
			// The minus operation is negation
			return Neg(ExprUtils.cast(ast.getOperand().accept(this), ClosedUnderNeg.class));
		case OP_PLUS:
			// The unary plus operator promotes the operand to an integral type
			// Since only integer variables are supported atm, this means a no-op
			return ast.getOperand().accept(this);
		case OP_NOT:
			return Not(ExprUtils.cast(ast.getOperand().accept(this), BoolType.class));
		case OP_POSTFIX_DECR:
		case OP_PREFIX_DECR:
		case OP_POSTFIX_INCR:
		case OP_PREFIX_INCR:
		default:
			// These operations should have been eliminated earlier.
			throw new RuntimeException("This code should not be reachable.");
		}
	}

	@Override
	public Expr<? extends Type> visit(NameExpressionAst ast) {
		if (!this.symbols.contains(ast.getName()))
			throw new TransformException(String.format("Use of undeclared identifier '%s'.", ast.getName()));

		return this.symbols.get(ast.getName()).getRef();
	}

	@Override
	public Expr<? extends Type> visit(FunctionCallExpressionAst ast) {
		String name = ast.getName();

		if (!this.symbols.contains(name)) {
			throw new RuntimeException(String.format("Use of undeclared identifier '%s'.", name));
		}

		Decl<? extends Type, ?> decl = this.symbols.get(name);
		if (!(decl instanceof ProcDecl<?>)) {
			throw new RuntimeException(String.format("Invalid use of function indirection.", name));
		}

		ProcDecl<? extends Type> proc = (ProcDecl<? extends Type>) decl;

		throw new UnsupportedOperationException("TODO: Function call");
	}

	@Override
	public Expr<? extends Type> visit(LiteralExpressionAst ast) {
		return Int(ast.getValue());
	}


	@Override
	public Decl<? extends Type, ?> visit(FunctionDefinitionAst ast) {
		ProcDecl<? extends Type> proc = Proc(ast.getName(), Collections.emptyList(), Int());
		Function func = new Function(ast.getName(), Int());

		this.functionTable.put(proc, func);

		return proc;
	}

	@Override
	public BasicBlock visit(IfStatementAst ast) {
		return null;
	}

	@Override
	public BasicBlock visit(DoStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BasicBlock visit(CompoundStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BasicBlock visit(DeclarationStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BasicBlock visit(ReturnStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BasicBlock visit(ExpressionStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BasicBlock visit(WhileStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BasicBlock visit(GotoStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BasicBlock visit(LabeledStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BasicBlock visit(NullStatementAst ast) {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	public GlobalContext visit(TranslationUnitAst ast) {
		GlobalContext context = new GlobalContext();

		// Add functions to the context
		ast.getDeclarations().stream().filter(s -> s instanceof FunctionDefinitionAst).map(s -> (FunctionDefinitionAst) s).forEach(s -> {
			context.addFunction(this.functionTable.get(s.accept(this)));
		});

		return context;
	}

	@Override
	public Decl<? extends Type, ?> visit(VarDeclarationAst ast) {
		throw new RuntimeException("This code should not be reachable");
	}

	@Override
	public BasicBlock visit(ForStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support for loops.");
	}

	@Override
	public BasicBlock visit(SwitchStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support switch statements.");
	}

	@Override
	public BasicBlock visit(CaseStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support case statements.");
	}

	@Override
	public BasicBlock visit(DefaultStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support default statements.");
	}

	@Override
	public BasicBlock visit(ContinueStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support continue statements.");
	}

	@Override
	public BasicBlock visit(BreakStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support break statements.");
	}

	@Override
	public Expr<? extends Type> visit(ExpressionListAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support expression lists.");
	}

	@Override
	public Decl<? extends Type, ?> visit(InitDeclaratorAst ast) {
		throw new UnsupportedOperationException("This code should not be reachable.");
	}

	@Override
	public Decl<? extends Type, ?> visit(FunctionDeclaratorAst ast) {
		throw new UnsupportedOperationException("This code should not be reachable.");
	}
}
