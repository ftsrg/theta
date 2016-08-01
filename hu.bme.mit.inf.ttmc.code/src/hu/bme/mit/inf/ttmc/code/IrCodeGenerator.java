package hu.bme.mit.inf.ttmc.code;

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
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;

import hu.bme.mit.inf.ttmc.code.ast.AssignmentInitializerAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DefaultStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionListAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ForStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionCallExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.GotoStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.IfStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst.Operator;
import hu.bme.mit.inf.ttmc.code.ast.visitor.DeclarationVisitor;
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
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.GlobalContext;
import hu.bme.mit.inf.ttmc.frontend.ir.InstructionBuilder;
import hu.bme.mit.inf.ttmc.frontend.ir.node.GotoNode;

import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


public class IrCodeGenerator implements
	ExpressionVisitor<Expr<? extends Type>>,
	StatementVisitor<Void>
{

	private SymbolTable<Decl<? extends Type, ?>> symbols = new SymbolTable<>();
	private InstructionBuilder builder;
	private final Map<String, BasicBlock> labels = new HashMap<>();
	private final Map<String, BasicBlock> gotos = new HashMap<>();

	public IrCodeGenerator(Function function) {
		this.builder = new InstructionBuilder(function);
		BasicBlock entry = this.builder.createBlock("entry");

		function.setEntryBlock(entry);

		this.builder.setInsertPoint(entry);
	}

	public void generate(FunctionDefinitionAst ast) {
		ast.getBody().accept(this);
		this.resolveGotos();
	}

	public void resolveGotos() {
		this.gotos.forEach((String label, BasicBlock source) -> {
			BasicBlock target = this.labels.get(label);
			if (null == target) {
				throw new IllegalArgumentException("Unknown label.");
			}

			if (source.getTerminator() instanceof GotoNode) {
				GotoNode gotoNode = (GotoNode) source.getTerminator();
				gotoNode.setTarget(target);
			}

		});
	}

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
	public Expr<? extends Type> visit(ExpressionListAst ast) {
		throw new UnsupportedOperationException("This code should not be reachble.");
	}

	@Override
	public Void visit(IfStatementAst ast) {
		Expr<? extends BoolType> cond = ExprUtils.cast(ast.getCondition().accept(this), BoolType.class);
		StatementAst then = ast.getThen();
		StatementAst elze = ast.getElse();

		// The original block
		BasicBlock branchBlock = this.builder.getInsertPoint();

		// The new blocks
		BasicBlock mergeBlock = this.builder.createBlock("merge");
		BasicBlock thenBlock = this.builder.createBlock("then");
		BasicBlock elzeBlock = this.builder.createBlock("else");

		this.builder.setInsertPoint(thenBlock);
		then.accept(this);
		this.builder.terminateInsertPoint(Goto(mergeBlock));

		this.builder.setInsertPoint(elzeBlock);
		if (elze != null) {
			elze.accept(this);
		}
		this.builder.terminateInsertPoint(Goto(mergeBlock));

		this.builder.setInsertPoint(branchBlock);
		this.builder.terminateInsertPoint(JumpIf(cond, thenBlock, elzeBlock));

		this.builder.setInsertPoint(mergeBlock);

		return null;
	}

	@Override
	public Void visit(CompoundStatementAst ast) {
		ast.getStatements().forEach(stmt -> stmt.accept(this));

		return null;
	}

	@Override
	public Void visit(DeclarationStatementAst ast) {
		DeclarationAst decl = ast.getDeclaration();

		if (decl instanceof VarDeclarationAst) {
			VarDeclarationAst varDecl = (VarDeclarationAst) decl;

			// Every declaration contains a single declarator because of the earlier transformations
			InitDeclaratorAst declarator = (InitDeclaratorAst) varDecl.getDeclarators().get(0); // TODO
			AssignmentInitializerAst initializer = (AssignmentInitializerAst) declarator.getInitializer();

			String name = declarator.getName();

			VarDecl<? extends Type> var = Var(name, Int());
			this.symbols.put(name, var);

			if (null != initializer) {
				Expr<? extends Type> initExpr = initializer.getExpression().accept(this);
				this.builder.insertNode(Assign(var, ExprUtils.cast(initExpr, var.getType().getClass())));
			}
		}

		return null;
	}

	@Override
	public Void visit(ReturnStatementAst ast) {
		this.builder.terminateInsertPoint(Goto(this.builder.getExitBlock()));

		return null;
	}

	@Override
	public Void visit(ExpressionStatementAst ast) {
		ExpressionAst exprAst = ast.getExpression();

		if (exprAst instanceof BinaryExpressionAst && ((BinaryExpressionAst) exprAst).getOperator() == Operator.OP_ASSIGN) {
			BinaryExpressionAst binary = (BinaryExpressionAst) exprAst;

			Expr<? extends Type> lhs = binary.getLeft().accept(this);
			Expr<?> rhs = binary.getRight().accept(this);

			if (!(lhs instanceof VarRefExpr<?>)) {
				throw new RuntimeException("Assignment lvalue can only be a variable reference.");
			}

			VarRefExpr<Type> left = (VarRefExpr<Type>) lhs;

			this.builder.insertNode(Assign(left.getDecl(), rhs));
		}

		return null;
	}

	@Override
	public Void visit(WhileStatementAst ast) {
		Expr<? extends BoolType> cond = ExprUtils.cast(ast.getCondition().accept(this), BoolType.class);
		StatementAst body = ast.getBody();

		// The original block
		BasicBlock branchBlock = this.builder.getInsertPoint();

		// The new blocks
		BasicBlock loopBlock = this.builder.createBlock("loop");
		BasicBlock bodyBlock = this.builder.createBlock("body");
		BasicBlock endBlock  = this.builder.createBlock("end");

		this.builder.setInsertPoint(loopBlock);
		this.builder.terminateInsertPoint(JumpIf(cond, bodyBlock, endBlock));

		this.builder.setInsertPoint(bodyBlock);
		body.accept(this);
		this.builder.terminateInsertPoint(Goto(loopBlock));

		this.builder.setInsertPoint(branchBlock);
		this.builder.terminateInsertPoint(Goto(loopBlock));

		this.builder.setInsertPoint(endBlock);

		return null;
	}

	@Override
	public Void visit(DoStatementAst ast) {
		Expr<? extends BoolType> cond = ExprUtils.cast(ast.getCondition().accept(this), BoolType.class);
		StatementAst body = ast.getBody();

		// The original block
		BasicBlock branchBlock = this.builder.getInsertPoint();

		// The new blocks
		BasicBlock loopBlock = this.builder.createBlock("loop");
		BasicBlock endBlock  = this.builder.createBlock("end");

		this.builder.setInsertPoint(loopBlock);
		body.accept(this);
		this.builder.terminateInsertPoint(JumpIf(cond, loopBlock, endBlock));

		this.builder.setInsertPoint(branchBlock);
		this.builder.terminateInsertPoint(Goto(loopBlock));

		this.builder.setInsertPoint(endBlock);
		return null;
	}

	@Override
	public Void visit(GotoStatementAst ast) {
		// terminate the current block with a temporary node
		this.builder.terminateInsertPoint(Goto(this.builder.getExitBlock()));
		this.gotos.put(ast.getLabel(), this.builder.getInsertPoint());

		BasicBlock bb = this.builder.createBlock("after_" + ast.getLabel());

		this.builder.setInsertPoint(bb);

		return null;
	}

	@Override
	public Void visit(LabeledStatementAst ast) {
		BasicBlock bb = this.builder.createBlock(ast.getLabel());

		this.labels.put(ast.getLabel(), bb);
		this.builder.terminateInsertPoint(Goto(bb));
		this.builder.setInsertPoint(bb);

		return null;
	}

	@Override
	public Void visit(NullStatementAst ast) {
		return null;
	}

	@Override
	public Void visit(ForStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support for loops.");
	}

	@Override
	public Void visit(SwitchStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support switch statements.");
	}

	@Override
	public Void visit(CaseStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support case statements.");
	}

	@Override
	public Void visit(DefaultStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support default statements.");
	}

	@Override
	public Void visit(ContinueStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support continue statements.");
	}

	@Override
	public Void visit(BreakStatementAst ast) {
		throw new UnsupportedOperationException("TransformProgramVisitor does not support break statements.");
	}

}
