package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.ParseException;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser;
import org.antlr.v4.codegen.model.decl.Decl;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mod;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class XSTSVisitor extends XstsDslBaseVisitor<Expr<?>> {

	private XSTS xsts;

	private final HashMap<String, BigInteger> literalToIntMap = new HashMap<>();
	private final HashMap<String, VarDecl<?>> nameToDeclMap = new HashMap<String, VarDecl<?>>();
	private final HashMap<VarDecl<?>, TypeDecl> varToTypeMap = new HashMap<>();
	private final HashMap<String, TypeDecl> nameToTypeMap = new HashMap<>();
	private final HashSet<Expr<BoolType>> initExprs = new HashSet<Expr<BoolType>>();
	private final HashSet<VarDecl<?>> ctrlVars = new HashSet<>();

	private final Pattern tempVarPattern = Pattern.compile("temp([0-9])+");
	private int counter;

	public XSTS getXsts() {
		return xsts;
	}

	@Override
	public Expr<?> visitXsts(XstsDslParser.XstsContext ctx) {

		counter = 0;

		for (XstsDslParser.TypeDeclarationContext typeDecl : ctx.typeDeclarations) {
			visitTypeDeclaration(typeDecl);
		}

		for (XstsDslParser.VariableDeclarationContext varDecl : ctx.variableDeclarations) {
			visitVariableDeclaration(varDecl);
		}

		xsts = new XSTS(nameToTypeMap.values(), varToTypeMap, ctrlVars, processNonDet(ctx.initAction.nonDet()), processNonDet(ctx.transitions.nonDet()), processNonDet(ctx.envAction.nonDet()), And(initExprs), cast(visitExpr(ctx.prop),Bool()));

		return null;
	}

	private void checkIfTempVar(String name) {
		if (tempVarPattern.matcher(name).matches()) throw new RuntimeException(name + " is reserved!");
	}

	@Override
	public Expr<?> visitTypeDeclaration(XstsDslParser.TypeDeclarationContext ctx) {
		checkIfTempVar(ctx.name.getText());
		if (nameToTypeMap.containsKey(ctx.name.getText()) || ctx.name.getText().equals("integer") || ctx.name.getText().equals("boolean")) {
			throw new ParseException(ctx, "Type '" + ctx.name.getText() + "' already exists!");
		}
		List<String> literals = new ArrayList<>();
		List<BigInteger> intValues = new ArrayList<>();
		for (XstsDslParser.TypeLiteralContext literal : ctx.literals) {
			checkIfTempVar(literal.name.getText());
			if (literals.contains(literal.name.getText()))
				throw new ParseException(ctx, "Duplicate literal '" + literal.name.getText() + "' in type '" + ctx.name.getText() + "'");
			if (literalToIntMap.containsKey(literal.name.getText())) {
				intValues.add(literalToIntMap.get(literal.name.getText()));
			} else {
				int val = counter++;
				intValues.add(BigInteger.valueOf(val));
				literalToIntMap.put(literal.name.getText(), BigInteger.valueOf(val));
			}
			literals.add(literal.name.getText());
		}
		TypeDecl decl = TypeDecl.of(ctx.name.getText(), literals, intValues);
		nameToTypeMap.put(decl.getName(), decl);
		return null;
	}

	private Type visitType(XstsDslParser.TypeNameContext ctx){
		if (ctx.BOOL() != null) {
			return BoolType.getInstance();
		} else if (ctx.INT() != null) {
			return IntType.getInstance();
		} else if (ctx.arrayType()!=null){
			var indexType = visitType(ctx.arrayType().indexType);
			var elemType = visitType(ctx.arrayType().elemType);
			return ArrayType.of(indexType,elemType);
		} else if (ctx.customType()!=null) {
			return IntType.getInstance();
		} else {
			throw new ParseException(ctx,"Couldn't parse type "+ctx.getText());
		}
	}


	@Override
	public Expr<?> visitVariableDeclaration(XstsDslParser.VariableDeclarationContext ctx) {
		checkIfTempVar(ctx.name.getText());
		if (nameToDeclMap.containsKey(ctx.name.getText())) {
			throw new ParseException(ctx, "Variable '" + ctx.name.getText() + "' already exists.");
		} else if (literalToIntMap.containsKey(ctx.name.getText())) {
			throw new ParseException(ctx, "'" + ctx.name.getText() + "' is a type literal, cannot declare variable with this name.");
		}

		Type type = visitType(ctx.type);
		VarDecl<?> decl = Decls.Var(ctx.name.getText(), type);
		if (ctx.type.customType()!=null){
			if (nameToTypeMap.containsKey(ctx.type.customType().name.getText())) {
				decl = Decls.Var(ctx.name.getText(), IntType.getInstance());
				varToTypeMap.put(decl, nameToTypeMap.get(ctx.type.customType().name.getText()));
			} else {
				throw new ParseException(ctx, "Unknown type '" + ctx.type.customType().name.getText() + "'.");
			}
		}

		if (ctx.CTRL() != null) ctrlVars.add(decl);
		nameToDeclMap.put(decl.getName(), decl);
		if (ctx.initValue != null) {
			initExprs.add(Eq(decl.getRef(), visitValue(ctx.initValue)));
		}
		return null;
	}

	@Override
	public Expr<?> visitExpr(XstsDslParser.ExprContext ctx) {
		if (ctx.iteExpression() == null) throw new ParseException(ctx, "Invalid expression.");
		return visitIteExpression(ctx.iteExpression());
	}

	@Override
	public Expr<?> visitIteExpression(XstsDslParser.IteExpressionContext ctx) {
		if (ctx.cond != null) {
			if (ctx.then == null || ctx.elze == null) throw new ParseException(ctx, "Invalid if-then-else expression.");
			return Ite(cast(visitExpr(ctx.cond),Bool()), visitExpr(ctx.then), visitExpr(ctx.elze));
		} else {
			if (ctx.implyExpression() == null) throw new ParseException(ctx, "Invalid expression.");
			return visitImplyExpression(ctx.implyExpression());
		}
	}

	@Override
	public Expr<?> visitImplyExpression(XstsDslParser.ImplyExpressionContext ctx) {
		if (ctx.ops.size() > 1) {
			return Imply(cast(visitOrExpr(ctx.ops.get(0)),Bool()), cast(visitOrExpr(ctx.ops.get(1)),Bool()));
		} else return visitOrExpr(ctx.ops.get(0));
	}

	@Override
	public Expr<?> visitOrExpr(XstsDslParser.OrExprContext ctx) {
		if (ctx.ops.size() == 1) return visitAndExpr(ctx.ops.get(0));
		List<Expr<BoolType>> ops = new ArrayList<>();
		for (XstsDslParser.AndExprContext child : ctx.ops) {
			ops.add(cast(visitAndExpr(child),Bool()));
		}
		return Or(ops);
	}

	@Override
	public Expr<?> visitAndExpr(XstsDslParser.AndExprContext ctx) {
		if (ctx.ops.size() == 1) return visitNotExpr(ctx.ops.get(0));
		List<Expr<BoolType>> ops = new ArrayList<>();
		for (XstsDslParser.NotExprContext child : ctx.ops) {
			ops.add(cast(visitNotExpr(child),Bool()));
		}
		return And(ops);
	}

	@Override
	public Expr<?> visitNotExpr(XstsDslParser.NotExprContext ctx) {
		if (ctx.ops.size() > 0) return Not(cast(visitNotExpr(ctx.ops.get(0)),Bool()));
		else return visitEqExpr(ctx.eqExpr());
	}

	@Override
	public Expr<?> visitEqExpr(XstsDslParser.EqExprContext ctx) {
		if (ctx.ops.size() > 1) {
			try{
				if (ctx.oper.EQ() != null) return Eq(visitRelationExpr(ctx.ops.get(0)), visitRelationExpr(ctx.ops.get(1)));
				else return Neq(visitRelationExpr(ctx.ops.get(0)), visitRelationExpr(ctx.ops.get(1)));
			} catch(Exception ex){
				throw new ParseException(ctx,ex.getMessage());
			}

		} else return visitRelationExpr(ctx.ops.get(0));
	}

	@Override
	public Expr<?> visitEqOperator(XstsDslParser.EqOperatorContext ctx) {
		return super.visitEqOperator(ctx);
	}

	@Override
	public Expr<?> visitRelationExpr(XstsDslParser.RelationExprContext ctx) {
		if (ctx.ops.size() > 1) {
			try{
				if (ctx.oper.LEQ() != null) {
					return Leq(visitAdditiveExpr(ctx.ops.get(0)), visitAdditiveExpr(ctx.ops.get(1)));
				} else if (ctx.oper.GEQ() != null) {
					return Geq(visitAdditiveExpr(ctx.ops.get(0)), visitAdditiveExpr(ctx.ops.get(1)));
				} else if (ctx.oper.LT() != null) {
					return Lt(visitAdditiveExpr(ctx.ops.get(0)), visitAdditiveExpr(ctx.ops.get(1)));
				} else if (ctx.oper.GT() != null) {
					return Gt(visitAdditiveExpr(ctx.ops.get(0)), visitAdditiveExpr(ctx.ops.get(1)));
				} else throw new ParseException(ctx, "Unsupported operation '" + ctx.oper.getText() + "'");
			} catch (Exception ex){
				throw new ParseException(ctx,ex.getMessage());
			}

		} else return visitAdditiveExpr(ctx.ops.get(0));
	}

	@Override
	public Expr<?> visitRelationOperator(XstsDslParser.RelationOperatorContext ctx) {
		return super.visitRelationOperator(ctx);
	}

	@Override
	public Expr<?> visitAdditiveExpr(XstsDslParser.AdditiveExprContext ctx) {
		Expr<?> res = visitMultiplicativeExpr(ctx.ops.get(0));
		for (int i = 1; i < ctx.ops.size(); i++) {
			if (ctx.opers.get(i - 1).PLUS() != null) {
				res = Add(res, visitMultiplicativeExpr(ctx.ops.get(i)));
			} else {
				res = Sub(res, visitMultiplicativeExpr(ctx.ops.get(i)));
			}
		}
		return res;

	}

	@Override
	public Expr<?> visitAdditiveOperator(XstsDslParser.AdditiveOperatorContext ctx) {
		return super.visitAdditiveOperator(ctx);
	}

	@Override
	public Expr<?> visitMultiplicativeExpr(XstsDslParser.MultiplicativeExprContext ctx) {
		Expr<?> res = visitNegExpr(ctx.ops.get(0));
		for (int i = 1; i < ctx.ops.size(); i++) {
			if (ctx.opers.get(i - 1).DIV() != null) {
				res = Div(res, visitNegExpr(ctx.ops.get(i)));
			} else if (ctx.opers.get(i - 1).MOD() != null) {
				res = Mod(cast(res,Int()), cast(visitNegExpr(ctx.ops.get(i)),Int()));
			} else if (ctx.opers.get(i - 1).MUL() != null) {
				res = Mul(res, visitNegExpr(ctx.ops.get(i)));
			} else {
				throw new ParseException(ctx, "Unsupported operation '" + ctx.opers.get(i - 1).getText() + "'");
			}
		}
		return res;
	}

	@Override
	public Expr<?> visitMultiplicativeOperator(XstsDslParser.MultiplicativeOperatorContext ctx) {
		return super.visitMultiplicativeOperator(ctx);
	}

	@Override
	public Expr<?> visitNegExpr(XstsDslParser.NegExprContext ctx) {
		if (ctx.ops.size() > 0) {
			return Neg(visitNegExpr(ctx.ops.get(0)));
		} else return visitAccessorExpr(ctx.accessorExpr());
	}

	@Override
	public Expr<?> visitAccessorExpr(XstsDslParser.AccessorExprContext ctx) {
		if(ctx.acc==null){
			return visitPrimaryExpr(ctx.op);
		} else {
			if(ctx.acc.readIndex!=null){
				return createArrayReadExpr(visitPrimaryExpr(ctx.op),ctx.acc.readIndex);
			}else if(ctx.acc.writeIndex!=null){
				return createArrayWriteExpr(visitPrimaryExpr(ctx.op),ctx.acc.writeIndex);
			}else throw new ParseException(ctx,"Invalid accessor expression.");
		}
	}

	private <T1 extends Type, T2 extends Type> Expr<?> createArrayReadExpr(final Expr<?> op,
																		   final XstsDslParser.ArrayReadAccessContext ctx) {
		checkArgument(op.getType() instanceof ArrayType);
		@SuppressWarnings("unchecked") final Expr<ArrayType<T1, T2>> array = (Expr<ArrayType<T1, T2>>) op;
		final Expr<T1> index = cast(ctx.index.accept(this), array.getType().getIndexType());
		return Read(array, index);
	}

	private <T1 extends Type, T2 extends Type> Expr<?> createArrayWriteExpr(final Expr<?> op,
																			final XstsDslParser.ArrayWriteAccessContext ctx) {
		checkArgument(op.getType() instanceof ArrayType);
		@SuppressWarnings("unchecked") final Expr<ArrayType<T1, T2>> array = (Expr<ArrayType<T1, T2>>) op;
		final Expr<T1> index = cast(ctx.index.accept(this), array.getType().getIndexType());
		final Expr<T2> elem = cast(ctx.elem.accept(this), array.getType().getElemType());
		return Write(array, index, elem);
	}

	@Override
	public Expr<?> visitPrimaryExpr(XstsDslParser.PrimaryExprContext ctx) {
		if (ctx.value() != null) return visitValue(ctx.value());
		else return visitParenExpr(ctx.parenExpr());
	}

	@Override
	public Expr<?> visitParenExpr(XstsDslParser.ParenExprContext ctx) {
		return visitExpr(ctx.ops.get(0));
	}

	@Override
	public Expr<?> visitValue(XstsDslParser.ValueContext ctx) {
		if (ctx.literal() != null) return visitLiteral(ctx.literal());
		else return visitReference(ctx.reference());
	}

	@Override
	public Expr<?> visitLiteral(XstsDslParser.LiteralContext ctx) {
		if (ctx.BOOLLIT() != null) {
			if (ctx.BOOLLIT().getText().equals("true")) return True();
			else return False();
		} else if (ctx.INTLIT() != null) {
			return Int(ctx.INTLIT().getText());
		} else if (ctx.arrLitExpr() != null){
			return visitArrLitExpr(ctx.arrLitExpr());
		} else {
			throw new ParseException(ctx, "Literal '" + ctx.getText() + "' could not be resolved to integer or boolean type.");
		}
	}

	@Override
	public Expr<?> visitArrLitExpr(XstsDslParser.ArrLitExprContext ctx) {
		return createArrayLitExpr(ctx);
	}

	@SuppressWarnings("unchecked")
	private <T1 extends Type, T2 extends Type> Expr<?> createArrayLitExpr(final XstsDslParser.ArrLitExprContext ctx) {
		checkArgument(ctx.indexExpr.size() > 0 || ctx.indexType != null);
		checkArgument(ctx.valueExpr.size() > 0 || ctx.indexType != null);

		final T1 indexType;
		final T2 valueType;

		if(ctx.indexType != null) {
			indexType = (T1) visitType(ctx.indexType);
		}
		else {
			indexType = (T1) visitExpr(ctx.indexExpr.get(0)).getType();
		}
		valueType = (T2) visitExpr(ctx.elseExpr).getType();

		final List<Tuple2<Expr<T1>, Expr<T2>>> elems = IntStream
				.range(0, ctx.indexExpr.size())
				.mapToObj(i -> Tuple2.of(
						cast(visitExpr(ctx.indexExpr.get(i)),indexType),
						cast(visitExpr(ctx.valueExpr.get(i)),valueType)
				))
				.collect(Collectors.toUnmodifiableList());

		final Expr<T2> elseExpr = cast(visitExpr(ctx.elseExpr),valueType);
		return Array(elems, elseExpr, ArrayType.of(indexType, valueType));
	}

	@Override
	public Expr<?> visitReference(XstsDslParser.ReferenceContext ctx) {
		checkIfTempVar(ctx.name.getText());
		if (literalToIntMap.containsKey(ctx.name.getText())) return Int(literalToIntMap.get(ctx.name.getText()));
		else if (nameToDeclMap.containsKey(ctx.name.getText())) return nameToDeclMap.get(ctx.name.getText()).getRef();
		else throw new ParseException(ctx, "Literal or reference '" + ctx.name.getText() + "' could not be resolved.");

	}

	public Stmt processAction(XstsDslParser.ActionContext ctx) {
		if (ctx.assignAction() != null) return processAssignAction(ctx.assignAction());
		else if (ctx.assumeAction() != null) return processAssumeAction(ctx.assumeAction());
		else if (ctx.havocAction() != null) return processHavocAction(ctx.havocAction());
		else if (ctx.nonDetAction() != null) return processNonDet(ctx.nonDetAction().nonDet());
		else if (ctx.ortAction() != null) return processOrt(ctx.ortAction());
		else return SkipStmt.getInstance();
	}

	public OrtStmt processOrt(XstsDslParser.OrtActionContext ctx) {
		List<Stmt> branches = new ArrayList<>();
		for (XstsDslParser.SequentialActionContext seq : ctx.branches) {
			branches.add(processSequentialAction(seq));
		}
		return OrtStmt.of(branches);
	}

	public NonDetStmt processNonDet(XstsDslParser.NonDetContext ctx) {
		List<Stmt> choices = new ArrayList<>();
		for (XstsDslParser.SequentialActionContext seq : ctx.choices) {
			choices.add(processSequentialAction(seq));
		}
		return NonDetStmt.of(choices);
	}

	public SequenceStmt processSequentialAction(XstsDslParser.SequentialActionContext ctx) {
		List<Stmt> stmts = new ArrayList<>();
		for (XstsDslParser.ActionContext action : ctx.actions) {
			stmts.add(processAction(action));
		}
		return SequenceStmt.of(stmts);
	}

	public AssumeStmt processAssumeAction(XstsDslParser.AssumeActionContext ctx) {
		return Stmts.Assume(cast(visitExpr(ctx.cond),Bool()));
	}

	public AssignStmt<?> processAssignAction(XstsDslParser.AssignActionContext ctx) {
		if (!nameToDeclMap.containsKey(ctx.lhs.getText())) {
			throw new ParseException(ctx, "Could not resolve variable '" + ctx.lhs.getText() + "'");
		}
		final VarDecl<?> var = nameToDeclMap.get(ctx.lhs.getText());
		final Expr<?> expr = visitExpr(ctx.rhs);
		if (expr.getType().equals(var.getType())) {
			@SuppressWarnings("unchecked") final VarDecl<Type> tVar = (VarDecl<Type>) var;
			@SuppressWarnings("unchecked") final Expr<Type> tExpr = (Expr<Type>) expr;
			return Assign(tVar, tExpr);
		} else {
			throw new IllegalArgumentException("Type of " + var + " is incompatible with " + expr);
		}
	}

	public HavocStmt<?> processHavocAction(XstsDslParser.HavocActionContext ctx) {
		if (!nameToDeclMap.containsKey(ctx.name.getText())) {
			throw new ParseException(ctx, "Could not resolve variable '" + ctx.name.getText() + "'");
		}
		return Stmts.Havoc(nameToDeclMap.get(ctx.name.getText()));
	}
}
