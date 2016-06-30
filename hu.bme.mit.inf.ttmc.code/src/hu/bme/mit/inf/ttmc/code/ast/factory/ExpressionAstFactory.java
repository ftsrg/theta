package hu.bme.mit.inf.ttmc.code.ast.factory;

import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst.Operator;

public class ExpressionAstFactory {

	public static BinaryExpressionAst Add(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_ADD);
	}

	public static BinaryExpressionAst Sub(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_SUB);
	}

	public static BinaryExpressionAst Mul(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_MUL);
	}

	public static BinaryExpressionAst Div(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_DIV);
	}

	public static BinaryExpressionAst Mod(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_MOD);
	}

	public static BinaryExpressionAst Assign(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_ASSIGN);
	}

	public static BinaryExpressionAst IsGt(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_GT);
	}

	public static BinaryExpressionAst IsGtEq(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_GTEQ);
	}

	public static BinaryExpressionAst IsLt(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_LT);
	}

	public static BinaryExpressionAst IsLtEq(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_LTEQ);
	}

	public static BinaryExpressionAst IsEq(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_EQ);
	}
	
	public static BinaryExpressionAst LogicAnd(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_LOGIC_AND);
	}
	
	public static BinaryExpressionAst LogicOr(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_LOGIC_OR);
	}
	
	public static NameExpressionAst Name(String name) {
		return new NameExpressionAst(name);
	}
	
	public static LiteralExpressionAst IntLit(int value) {
		return new LiteralExpressionAst(value);
	}
	
	public static UnaryExpressionAst PrefixIncr(ExpressionAst operand) {
		return new UnaryExpressionAst(operand, Operator.OP_PREFIX_INCR);
	}
	
	public static UnaryExpressionAst PostfixIncr(ExpressionAst operand) {
		return new UnaryExpressionAst(operand, Operator.OP_POSTFIX_INCR);
	}
	
	public static UnaryExpressionAst PrefixDecr(ExpressionAst operand) {
		return new UnaryExpressionAst(operand, Operator.OP_PREFIX_DECR);
	}
	
	public static UnaryExpressionAst PostfixDecr(ExpressionAst operand) {
		return new UnaryExpressionAst(operand, Operator.OP_POSTFIX_DECR);
	}
	
}
