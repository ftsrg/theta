package hu.bme.mit.inf.ttmc.code.ast.factory;

import hu.bme.mit.inf.ttmc.code.ast.BinaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.ExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.LiteralExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.NameExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst;
import hu.bme.mit.inf.ttmc.code.ast.UnaryExpressionAst.Operator;

public class ExpressionAstFactory {

	public static BinaryExpressionAst add(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_ADD);
	}

	public static BinaryExpressionAst sub(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_SUB);
	}

	public static BinaryExpressionAst mul(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_MUL);
	}

	public static BinaryExpressionAst div(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_DIV);
	}

	public static BinaryExpressionAst assign(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_ASSIGN);
	}

	public static BinaryExpressionAst isGt(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_GT);
	}

	public static BinaryExpressionAst isGtEq(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_GTEQ);
	}

	public static BinaryExpressionAst isLt(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_LT);
	}

	public static BinaryExpressionAst isLtEq(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_LTEQ);
	}

	public static BinaryExpressionAst isEq(ExpressionAst left, ExpressionAst right) {
		return new BinaryExpressionAst(left, right, BinaryExpressionAst.Operator.OP_IS_EQ);
	}
	
	public static NameExpressionAst name(String name) {
		return new NameExpressionAst(name);
	}
	
	public static LiteralExpressionAst lit(int value) {
		return new LiteralExpressionAst(value);
	}
	
	public static UnaryExpressionAst prefixIncr(ExpressionAst operand) {
		return new UnaryExpressionAst(operand, Operator.OP_PREFIX_INCR);
	}
	
	public static UnaryExpressionAst postfixIncr(ExpressionAst operand) {
		return new UnaryExpressionAst(operand, Operator.OP_POSTFIX_INCR);
	}
	
	public static UnaryExpressionAst prefixDecr(ExpressionAst operand) {
		return new UnaryExpressionAst(operand, Operator.OP_PREFIX_DECR);
	}
	
	public static UnaryExpressionAst postfixDecr(ExpressionAst operand) {
		return new UnaryExpressionAst(operand, Operator.OP_POSTFIX_DECR);
	}
	
}
