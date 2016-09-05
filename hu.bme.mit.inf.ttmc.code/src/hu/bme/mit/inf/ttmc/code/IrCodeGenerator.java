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
import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.Assert;
import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.Assign;
import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.Goto;
import static hu.bme.mit.inf.ttmc.frontend.ir.node.NodeFactory.JumpIf;

import java.util.EmptyStackException;
import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import hu.bme.mit.inf.ttmc.code.ast.AssignmentInitializerAst;
import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.BreakStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CaseStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.CompoundStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ContinueStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclarationStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.DeclaratorAst;
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
import hu.bme.mit.inf.ttmc.code.ast.InitializerAst;
import hu.bme.mit.inf.ttmc.code.ast.LabeledStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NullStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.ReturnStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.SwitchStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.WhileStatementAst;
import hu.bme.mit.inf.ttmc.code.ast.visitor.ExpressionVisitor;
import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;
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
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.GlobalContext;
import hu.bme.mit.inf.ttmc.frontend.ir.InstructionBuilder;
import hu.bme.mit.inf.ttmc.frontend.ir.node.BranchTableNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.EntryNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.GotoNode;

public class IrCodeGenerator implements
	ExpressionVisitor<Expr<? extends Type>>,
	StatementVisitor<Void>
{

	private final SymbolTable<Decl<? extends Type, ?>> symbols = new SymbolTable<>();
	private final InstructionBuilder builder;
	private final GlobalContext context;

	private final Map<String, BasicBlock> labels = new HashMap<>();
	private final Map<String, BasicBlock> gotos = new HashMap<>();

	private final Stack<BasicBlock> breakTargets = new Stack<>();
	private final Stack<BasicBlock> continueTargets = new Stack<>();
	private final Stack<Map<Expr<? extends Type>, BasicBlock>> switchTargets = new Stack<>();
	private final Stack<BasicBlock> switchDefaults = new Stack<>();

	private int tmpId = 0;

	public IrCodeGenerator(GlobalContext context, Function function) {
		this.builder = new InstructionBuilder(function);
		this.context = context;

		BasicBlock entry = this.builder.createBlock("entry");

		BasicBlock codeEntry = this.builder.createBlock("code_entry");
		entry.terminate(new EntryNode(codeEntry));

		function.setEntryBlock(entry);

		this.builder.setInsertPoint(codeEntry);
	}

	public void generate(FunctionDefinitionAst ast) {
		ast.getBody().accept(this);
		this.resolveGotos();
		this.builder.getFunction().normalize();
	}

	private void resolveGotos() {
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
			case OP_ASSIGN: {
				if (!(left instanceof VarRefExpr<?>)) {
					throw new ParserException("Cannot assign an rvalue.");
				}

				VarRefExpr<? extends Type> varRef = (VarRefExpr<? extends Type>) left;
				this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(right, varRef.getType().getClass())));

				return varRef;
			}
			case OP_ADD_ASSIGN: {
				if (!(left instanceof VarRefExpr<?>)) {
					throw new ParserException("Cannot assign an rvalue.");
				}

				if (!(left.getType() instanceof ClosedUnderAdd)) {
					throw new ParserException("Attempting to add an expression with an incompatible type: " + left.getType().getClass());
				}

				@SuppressWarnings("unchecked")
				VarRefExpr<? extends ClosedUnderAdd> varRef = (VarRefExpr<? extends ClosedUnderAdd>) left;
				Expr<? extends ClosedUnderAdd> rightCasted  = ExprUtils.cast(right, ClosedUnderAdd.class);

				this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(Add(varRef, rightCasted), varRef.getType().getClass())));

				return varRef;
			}
			case OP_DIV_ASSIGN: {
				if (!(left instanceof VarRefExpr<?>)) {
					throw new ParserException("Cannot assign an rvalue.");
				}

				if (!(left.getType() instanceof IntType)) {
					throw new ParserException("Attempting to divide an expression with an incompatible type: " + left.getType().getClass());
				}

				@SuppressWarnings("unchecked")
				VarRefExpr<? extends IntType> varRef = (VarRefExpr<? extends IntType>) left;
				Expr<? extends IntType> rightCasted  = ExprUtils.cast(right, IntType.class);

				this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(IntDiv(varRef, rightCasted), varRef.getType().getClass())));

				return varRef;
			}
			case OP_MOD_ASSIGN: {
				if (!(left instanceof VarRefExpr<?>)) {
					throw new ParserException("Cannot assign an rvalue.");
				}

				if (!(left.getType() instanceof IntType)) {
					throw new ParserException("Attempting to mod an expression with an incompatible type: " + left.getType().getClass());
				}

				@SuppressWarnings("unchecked")
				VarRefExpr<? extends IntType> varRef = (VarRefExpr<? extends IntType>) left;
				Expr<? extends IntType> rightCasted  = ExprUtils.cast(right, IntType.class);

				this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(Mod(varRef, rightCasted), varRef.getType().getClass())));

				return varRef;
			}
			case OP_MUL_ASSIGN: {
				if (!(left instanceof VarRefExpr<?>)) {
					throw new ParserException("Cannot assign an rvalue.");
				}

				if (!(left.getType() instanceof ClosedUnderMul)) {
					throw new ParserException("Attempting to multiply an expression with an incompatible type: " + left.getType().getClass());
				}

				@SuppressWarnings("unchecked")
				VarRefExpr<? extends ClosedUnderMul> varRef = (VarRefExpr<? extends ClosedUnderMul>) left;
				Expr<? extends ClosedUnderMul> rightCasted  = ExprUtils.cast(right, ClosedUnderMul.class);

				this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(Mul(varRef, rightCasted), varRef.getType().getClass())));

				return varRef;
			}
			case OP_SUB_ASSIGN: {
				if (!(left instanceof VarRefExpr<?>)) {
					throw new ParserException("Cannot assign an rvalue.");
				}

				if (!(left.getType() instanceof ClosedUnderSub)) {
					throw new ParserException("Attempting to substract an expression with an incompatible type: " + left.getType().getClass());
				}

				@SuppressWarnings("unchecked")
				VarRefExpr<? extends ClosedUnderSub> varRef = (VarRefExpr<? extends ClosedUnderSub>) left;
				Expr<? extends ClosedUnderSub> rightCasted  = ExprUtils.cast(right, ClosedUnderSub.class);

				this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(Sub(varRef, rightCasted), varRef.getType().getClass())));

				return varRef;
			}
			default:
				throw new AssertionError("This code should not be reachable.");
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
		case OP_POSTFIX_INCR: {
			Expr<? extends ClosedUnderAdd> expr = ExprUtils.cast(ast.getOperand().accept(this), ClosedUnderAdd.class);
			if (!(expr instanceof VarRefExpr<?>)) {
				throw new ParserException("Lvalue required as increment operand.");
			}

			VarRefExpr<? extends ClosedUnderAdd> varRef = (VarRefExpr<? extends ClosedUnderAdd>) expr;
			VarDecl<? extends ClosedUnderAdd> tmp  = Var("tmp_" + this.tmpId++, varRef.getType());

			this.builder.insertNode(Assign(tmp, ExprUtils.cast(varRef, tmp.getType().getClass())));
			this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(Add(varRef, Int(1)), varRef.getType().getClass())));

			return tmp.getRef();
		}
		case OP_PREFIX_INCR: {
			Expr<? extends ClosedUnderAdd> expr = ExprUtils.cast(ast.getOperand().accept(this), ClosedUnderAdd.class);
			if (!(expr instanceof VarRefExpr<?>)) {
				throw new ParserException("Lvalue required as increment operand.");
			}

			VarRefExpr<? extends ClosedUnderAdd> varRef = (VarRefExpr<? extends ClosedUnderAdd>) expr;

			this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(Add(varRef, Int(1)), varRef.getType().getClass())));

			return varRef;
		}
		case OP_POSTFIX_DECR: {
			Expr<? extends ClosedUnderSub> expr = ExprUtils.cast(ast.getOperand().accept(this), ClosedUnderSub.class);
			if (!(expr instanceof VarRefExpr<?>)) {
				throw new ParserException("Lvalue required as increment operand.");
			}

			VarRefExpr<? extends ClosedUnderSub> varRef = (VarRefExpr<? extends ClosedUnderSub>) expr;
			VarDecl<? extends ClosedUnderSub> tmp  = Var("tmp_" + this.tmpId++, varRef.getType());

			this.builder.insertNode(Assign(tmp, ExprUtils.cast(varRef, tmp.getType().getClass())));
			this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(Sub(varRef, Int(1)), varRef.getType().getClass())));

			return tmp.getRef();
		}
		case OP_PREFIX_DECR: {
			Expr<? extends ClosedUnderSub> expr = ExprUtils.cast(ast.getOperand().accept(this), ClosedUnderSub.class);
			if (!(expr instanceof VarRefExpr<?>)) {
				throw new ParserException("Lvalue required as increment operand.");
			}

			VarRefExpr<? extends ClosedUnderSub> varRef = (VarRefExpr<? extends ClosedUnderSub>) expr;

			this.builder.insertNode(Assign(varRef.getDecl(), ExprUtils.cast(Sub(varRef, Int(1)), varRef.getType().getClass())));

			return varRef;
		}
		default:
			throw new AssertionError("This code should not be reachable.");
		}
	}

	@Override
	public Expr<? extends Type> visit(NameExpressionAst ast) {
		if (!this.symbols.contains(ast.getName()))
			throw new ParserException(String.format("Use of undeclared identifier '%s'.", ast.getName()));

		return this.symbols.get(ast.getName()).getRef();
	}

	@Override
	public Expr<? extends Type> visit(FunctionCallExpressionAst ast) {
		throw new AssertionError("TODO: Function call");
	}

	@Override
	public Expr<? extends Type> visit(LiteralExpressionAst ast) {
		return Int(ast.getValue());
	}

	@Override
	public Expr<? extends Type> visit(ExpressionListAst ast) {
		if (ast.getExpressions().size() == 0)
			throw new ParserException("Expression lists cannot be empty");

		Expr<? extends Type> res = null;
		for (ExpressionAst expr : ast.getExpressions()) {
			res = expr.accept(this);
		}

		return res;
	}

	@Override
	public Void visit(IfStatementAst ast) {
		Expr<? extends BoolType> cond = this.createCondition(ast.getCondition());
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

		this.symbols.pushScope();
		for (StatementAst stmt : ast.getStatements()) {
			stmt.accept(this);
		}
		this.symbols.popScope();

		return null;
	}

	@Override
	public Void visit(DeclarationStatementAst ast) {
		DeclarationAst decl = ast.getDeclaration();

		if (decl instanceof VarDeclarationAst) {
			VarDeclarationAst varDecl = (VarDeclarationAst) decl;

			for (DeclaratorAst declarator : varDecl.getDeclarators()) {
				String name = declarator.getName();

				VarDecl<? extends Type> var;
				if (this.symbols.currentScopeContains(name)) { // A variable was redeclared in the current scope
					throw new ParserException(String.format("Cannot redeclare variable '%s'.", name));
				} else if (this.symbols.contains(name)) { // The variable is declared in an outer scope, we need to override it for the current one
					var = Var(name + "__conf" + this.tmpId++, Int());
					this.symbols.put(name, var); // The expressions will still reference this tmp variable by the original name, so we must store it with that.
				} else {
					var = Var(name, Int());
					this.symbols.put(name, var);
				}

				if (declarator instanceof InitDeclaratorAst) {
					InitializerAst initializer = ((InitDeclaratorAst) declarator).getInitializer();
					if (initializer != null) {
						if (initializer instanceof AssignmentInitializerAst) {
							Expr<? extends Type> initExpr = ((AssignmentInitializerAst) initializer).getExpression().accept(this);
							this.builder.insertNode(Assign(var, ExprUtils.cast(initExpr, var.getType().getClass())));
						} else {
							throw new UnsupportedOperationException("Unsupported initializer clause");
						}
					}
				}
			}
		} else {
			throw new UnsupportedOperationException("Unsupported declaration clause");
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

		if (exprAst instanceof FunctionCallExpressionAst) {
			FunctionCallExpressionAst func = (FunctionCallExpressionAst) ast.getExpression();

			if (func.getName().equals("assert")) {
				ExpressionAst cond = func.getParams().get(0); // The first parameter is the condition
				this.builder.insertNode(Assert(ExprUtils.cast(cond.accept(this), BoolType.class)));
			}
		} else {
			exprAst.accept(this);
		}

		return null;
	}

	@Override
	public Void visit(WhileStatementAst ast) {
		Expr<? extends BoolType> cond = this.createCondition(ast.getCondition());
		StatementAst body = ast.getBody();

		// The original block
		BasicBlock branchBlock = this.builder.getInsertPoint();

		// The new blocks
		BasicBlock loopBlock = this.builder.createBlock("loop");
		BasicBlock bodyBlock = this.builder.createBlock("body");
		BasicBlock endBlock  = this.builder.createBlock("end");

		this.builder.setInsertPoint(loopBlock);
		this.builder.terminateInsertPoint(JumpIf(cond, bodyBlock, endBlock));

		this.breakTargets.push(endBlock);
		this.continueTargets.push(loopBlock);

		this.builder.setInsertPoint(bodyBlock);
		body.accept(this);
		this.builder.terminateInsertPoint(Goto(loopBlock));

		this.breakTargets.pop();
		this.continueTargets.pop();

		this.builder.setInsertPoint(branchBlock);
		this.builder.terminateInsertPoint(Goto(loopBlock));

		this.builder.setInsertPoint(endBlock);

		return null;
	}

	@Override
	public Void visit(DoStatementAst ast) {
		Expr<? extends BoolType> cond = this.createCondition(ast.getCondition());
		StatementAst body = ast.getBody();

		// The original block
		BasicBlock branchBlock = this.builder.getInsertPoint();

		// The new blocks
		BasicBlock loopBlock = this.builder.createBlock("loop");
		BasicBlock endBlock  = this.builder.createBlock("end");

		this.breakTargets.push(endBlock);
		this.continueTargets.push(loopBlock);

		this.builder.setInsertPoint(loopBlock);
		body.accept(this);
		this.builder.terminateInsertPoint(JumpIf(cond, loopBlock, endBlock));

		this.breakTargets.pop();
		this.continueTargets.pop();

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
		ast.getStatement().accept(this);

		return null;
	}

	@Override
	public Void visit(NullStatementAst ast) {
		return null;
	}

	@Override
	public Void visit(ForStatementAst ast) {
		StatementAst body = ast.getBody();

		// The original block
		BasicBlock branchBlock = this.builder.getInsertPoint();

		// The new blocks
		BasicBlock headerBlock = this.builder.createBlock("header");
		BasicBlock bodyBlock = this.builder.createBlock("body");
		BasicBlock incrBlock = this.builder.createBlock("incr");

		BasicBlock endBlock  = this.builder.createBlock("end");

		ast.getInit().accept(this);
		Expr<? extends BoolType> cond = this.createCondition(ast.getCondition());

		this.builder.setInsertPoint(headerBlock);
		this.builder.terminateInsertPoint(JumpIf(cond, bodyBlock, endBlock));

		this.breakTargets.push(endBlock);
		this.continueTargets.push(incrBlock);

		this.builder.setInsertPoint(bodyBlock);
		body.accept(this);
		this.builder.terminateInsertPoint(Goto(incrBlock));

		this.breakTargets.pop();
		this.continueTargets.pop();

		this.builder.setInsertPoint(incrBlock);
		ast.getIteration().accept(this);
		this.builder.terminateInsertPoint(Goto(headerBlock));

		this.builder.setInsertPoint(branchBlock);
		this.builder.terminateInsertPoint(Goto(headerBlock));

		this.builder.setInsertPoint(endBlock);

		return null;
	}

	@Override
	public Void visit(SwitchStatementAst ast) {
		Expr<? extends Type> cond = ast.getExpression().accept(this);

		BasicBlock merge = this.builder.createBlock("merge");
		BasicBlock body  = this.builder.createBlock("body");
		BasicBlock source = this.builder.getInsertPoint();

		this.switchTargets.push(new HashMap<>());
		this.switchDefaults.push(merge);
		this.breakTargets.push(merge);

		this.builder.setInsertPoint(body);
		ast.getBody().accept(this);

		if (this.builder.getInsertPoint() != body) {
			this.builder.terminateInsertPoint(Goto(merge));
		}

		if (body.isTerminated()) {
			body.clearTerminator();
		}

		this.builder.setInsertPoint(source);
		this.builder.terminateInsertPoint(Goto(body));
		this.builder.setInsertPoint(body);

		BranchTableNode branchTable = new BranchTableNode(cond);
		this.switchTargets.peek().forEach((value, target) -> {
			branchTable.addTarget(value, target);
		});

		branchTable.setDefaultTarget(this.switchDefaults.peek());
		this.builder.terminateInsertPoint(branchTable);

		this.breakTargets.pop();
		this.switchDefaults.pop();
		this.switchTargets.pop();

		this.builder.setInsertPoint(merge);

		return null;
	}

	@Override
	public Void visit(CaseStatementAst ast) {
		Expr<? extends Type> expr = ast.getExpression().accept(this);
		BasicBlock after = this.builder.createBlock("case_" + this.tmpId++);

		this.builder.terminateInsertPoint(Goto(after));
		this.builder.setInsertPoint(after);

		this.switchTargets.peek().put(expr, after);

		return null;
	}

	@Override
	public Void visit(DefaultStatementAst ast) {
		BasicBlock after = this.builder.createBlock("def_" + this.tmpId++);

		this.builder.terminateInsertPoint(Goto(after));
		this.builder.setInsertPoint(after);

		this.switchDefaults.pop();
		this.switchDefaults.push(after);

		return null;
	}

	@Override
	public Void visit(ContinueStatementAst ast) {
		try {
			BasicBlock target = this.continueTargets.peek();
			BasicBlock insertPoint = this.builder.createBlock("after_cont");

			this.builder.terminateInsertPoint(Goto(target));
			this.builder.setInsertPoint(insertPoint);
		} catch (EmptyStackException ex) {
			throw new ParserException("Continue statement not within a loop", ex);
		}

		return null;
	}

	@Override
	public Void visit(BreakStatementAst ast) {
		try {
			BasicBlock target = this.breakTargets.peek();
			BasicBlock insertPoint = this.builder.createBlock("after_break");

			this.builder.terminateInsertPoint(Goto(target));
			this.builder.setInsertPoint(insertPoint);
		} catch (EmptyStackException ex) {
			throw new ParserException("Break statement not within a loop or switch", ex);
		}

		return null;
	}

	private Expr<? extends BoolType> createCondition(ExpressionAst ast) {
		Expr<? extends Type> cond = ast.accept(this);

		if (cond.getType() instanceof BoolType) {
			return ExprUtils.cast(cond, BoolType.class);
		} else if (cond.getType() instanceof IntType) {
			// Cast integers to booleans by comparing them to 0.
			// If integers are used as booleans, 0 stands for false, everything else stands for true,
			// so a single EXPR != 0 comparation will do the required cast
			return Neq(cond, Int(0));
		} else {
			throw new ParserException("Branch conditionals can only be booleans or integers");
		}
	}

}
