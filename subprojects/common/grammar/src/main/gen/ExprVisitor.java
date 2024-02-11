// Generated from /home/levente/Documents/University/theta-fresh/subprojects/common/grammar/src/main/antlr/Expr.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link ExprParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface ExprVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link ExprParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpr(ExprParser.ExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#exprList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExprList(ExprParser.ExprListContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#funcLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncLitExpr(ExprParser.FuncLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#iteExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIteExpr(ExprParser.IteExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#iffExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIffExpr(ExprParser.IffExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#implyExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitImplyExpr(ExprParser.ImplyExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuantifiedExpr(ExprParser.QuantifiedExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#forallExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitForallExpr(ExprParser.ForallExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#existsExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExistsExpr(ExprParser.ExistsExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#fpFuncExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFpFuncExpr(ExprParser.FpFuncExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#orExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOrExpr(ExprParser.OrExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#xorExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitXorExpr(ExprParser.XorExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#andExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAndExpr(ExprParser.AndExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#notExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNotExpr(ExprParser.NotExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#equalityExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEqualityExpr(ExprParser.EqualityExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#relationExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRelationExpr(ExprParser.RelationExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bitwiseOrExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseOrExpr(ExprParser.BitwiseOrExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bitwiseXorExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseXorExpr(ExprParser.BitwiseXorExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bitwiseAndExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseAndExpr(ExprParser.BitwiseAndExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bitwiseShiftExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseShiftExpr(ExprParser.BitwiseShiftExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#additiveExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAdditiveExpr(ExprParser.AdditiveExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMultiplicativeExpr(ExprParser.MultiplicativeExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bvConcatExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvConcatExpr(ExprParser.BvConcatExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bvExtendExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvExtendExpr(ExprParser.BvExtendExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#unaryExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUnaryExpr(ExprParser.UnaryExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bitwiseNotExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseNotExpr(ExprParser.BitwiseNotExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#functionCall}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunctionCall(ExprParser.FunctionCallContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#arrayRead}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayRead(ExprParser.ArrayReadContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#arrayWrite}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayWrite(ExprParser.ArrayWriteContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#primeExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrimeExpr(ExprParser.PrimeExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bvExtract}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvExtract(ExprParser.BvExtractContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#primaryExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrimaryExpr(ExprParser.PrimaryExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#trueExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTrueExpr(ExprParser.TrueExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#falseExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFalseExpr(ExprParser.FalseExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#intLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntLitExpr(ExprParser.IntLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#ratLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatLitExpr(ExprParser.RatLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#arrLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrLitExpr(ExprParser.ArrLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bvLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvLitExpr(ExprParser.BvLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#fpLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFpLitExpr(ExprParser.FpLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#idExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdExpr(ExprParser.IdExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#parenExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenExpr(ExprParser.ParenExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl(ExprParser.DeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#declList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDeclList(ExprParser.DeclListContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#type}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitType(ExprParser.TypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#typeList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeList(ExprParser.TypeListContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#boolType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolType(ExprParser.BoolTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#intType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntType(ExprParser.IntTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#ratType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatType(ExprParser.RatTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#funcType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncType(ExprParser.FuncTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#arrayType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayType(ExprParser.ArrayTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#bvType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvType(ExprParser.BvTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link ExprParser#fpType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFpType(ExprParser.FpTypeContext ctx);
}