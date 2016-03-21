package hu.bme.mit.inf.ttmc.code.ast;

abstract public class AstVisitor<R> {

	abstract public R visit(AstNode ast);
	abstract public R visit(NameExpressionAst ast);
	abstract public R visit(LiteralExpressionAst ast);
	abstract public R visit(BinaryExpressionAst ast);
	abstract public R visit(FunctionAst ast);
	abstract public R visit(CompoundStatementAst ast);
	abstract public R visit(ExpressionStatementAst ast);
	
}
