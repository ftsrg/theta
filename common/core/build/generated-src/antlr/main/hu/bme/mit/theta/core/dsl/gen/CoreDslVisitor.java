// Generated from CoreDsl.g4 by ANTLR 4.7.2
package hu.bme.mit.theta.core.dsl.gen;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link CoreDslParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface CoreDslVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl(CoreDslParser.DeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#declList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDeclList(CoreDslParser.DeclListContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#type}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitType(CoreDslParser.TypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#typeList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeList(CoreDslParser.TypeListContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#boolType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolType(CoreDslParser.BoolTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#intType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntType(CoreDslParser.IntTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#ratType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatType(CoreDslParser.RatTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#funcType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncType(CoreDslParser.FuncTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#arrayType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayType(CoreDslParser.ArrayTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bvType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvType(CoreDslParser.BvTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpr(CoreDslParser.ExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#exprList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExprList(CoreDslParser.ExprListContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#funcLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncLitExpr(CoreDslParser.FuncLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#iteExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIteExpr(CoreDslParser.IteExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#iffExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIffExpr(CoreDslParser.IffExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#implyExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitImplyExpr(CoreDslParser.ImplyExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuantifiedExpr(CoreDslParser.QuantifiedExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#forallExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitForallExpr(CoreDslParser.ForallExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#existsExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExistsExpr(CoreDslParser.ExistsExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#orExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOrExpr(CoreDslParser.OrExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#andExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAndExpr(CoreDslParser.AndExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#notExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNotExpr(CoreDslParser.NotExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#equalityExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEqualityExpr(CoreDslParser.EqualityExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#relationExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRelationExpr(CoreDslParser.RelationExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bitwiseOrExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseOrExpr(CoreDslParser.BitwiseOrExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bitwiseXorExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseXorExpr(CoreDslParser.BitwiseXorExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bitwiseAndExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseAndExpr(CoreDslParser.BitwiseAndExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bitwiseShiftExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseShiftExpr(CoreDslParser.BitwiseShiftExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#additiveExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAdditiveExpr(CoreDslParser.AdditiveExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMultiplicativeExpr(CoreDslParser.MultiplicativeExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bvConcatExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvConcatExpr(CoreDslParser.BvConcatExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bvExtendExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvExtendExpr(CoreDslParser.BvExtendExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#unaryExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUnaryExpr(CoreDslParser.UnaryExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bitwiseNotExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseNotExpr(CoreDslParser.BitwiseNotExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#accessorExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAccessorExpr(CoreDslParser.AccessorExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#access}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAccess(CoreDslParser.AccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#funcAccess}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncAccess(CoreDslParser.FuncAccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#arrayAccess}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayAccess(CoreDslParser.ArrayAccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#primeAccess}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrimeAccess(CoreDslParser.PrimeAccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bvExtractAccess}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvExtractAccess(CoreDslParser.BvExtractAccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#primaryExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrimaryExpr(CoreDslParser.PrimaryExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#trueExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTrueExpr(CoreDslParser.TrueExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#falseExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFalseExpr(CoreDslParser.FalseExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#intLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntLitExpr(CoreDslParser.IntLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#ratLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatLitExpr(CoreDslParser.RatLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#bvLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvLitExpr(CoreDslParser.BvLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#idExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdExpr(CoreDslParser.IdExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#parenExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenExpr(CoreDslParser.ParenExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStmt(CoreDslParser.StmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#stmtList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStmtList(CoreDslParser.StmtListContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#assignStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssignStmt(CoreDslParser.AssignStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#havocStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitHavocStmt(CoreDslParser.HavocStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link CoreDslParser#assumeStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssumeStmt(CoreDslParser.AssumeStmtContext ctx);
}