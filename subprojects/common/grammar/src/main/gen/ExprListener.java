// Generated from /home/levente/Documents/University/theta-fresh/subprojects/common/grammar/src/main/antlr/Expr.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link ExprParser}.
 */
public interface ExprListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link ExprParser#expr}.
	 * @param ctx the parse tree
	 */
	void enterExpr(ExprParser.ExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#expr}.
	 * @param ctx the parse tree
	 */
	void exitExpr(ExprParser.ExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#exprList}.
	 * @param ctx the parse tree
	 */
	void enterExprList(ExprParser.ExprListContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#exprList}.
	 * @param ctx the parse tree
	 */
	void exitExprList(ExprParser.ExprListContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#funcLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterFuncLitExpr(ExprParser.FuncLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#funcLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitFuncLitExpr(ExprParser.FuncLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#iteExpr}.
	 * @param ctx the parse tree
	 */
	void enterIteExpr(ExprParser.IteExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#iteExpr}.
	 * @param ctx the parse tree
	 */
	void exitIteExpr(ExprParser.IteExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#iffExpr}.
	 * @param ctx the parse tree
	 */
	void enterIffExpr(ExprParser.IffExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#iffExpr}.
	 * @param ctx the parse tree
	 */
	void exitIffExpr(ExprParser.IffExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#implyExpr}.
	 * @param ctx the parse tree
	 */
	void enterImplyExpr(ExprParser.ImplyExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#implyExpr}.
	 * @param ctx the parse tree
	 */
	void exitImplyExpr(ExprParser.ImplyExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 */
	void enterQuantifiedExpr(ExprParser.QuantifiedExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 */
	void exitQuantifiedExpr(ExprParser.QuantifiedExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#forallExpr}.
	 * @param ctx the parse tree
	 */
	void enterForallExpr(ExprParser.ForallExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#forallExpr}.
	 * @param ctx the parse tree
	 */
	void exitForallExpr(ExprParser.ForallExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#existsExpr}.
	 * @param ctx the parse tree
	 */
	void enterExistsExpr(ExprParser.ExistsExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#existsExpr}.
	 * @param ctx the parse tree
	 */
	void exitExistsExpr(ExprParser.ExistsExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#fpFuncExpr}.
	 * @param ctx the parse tree
	 */
	void enterFpFuncExpr(ExprParser.FpFuncExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#fpFuncExpr}.
	 * @param ctx the parse tree
	 */
	void exitFpFuncExpr(ExprParser.FpFuncExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#orExpr}.
	 * @param ctx the parse tree
	 */
	void enterOrExpr(ExprParser.OrExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#orExpr}.
	 * @param ctx the parse tree
	 */
	void exitOrExpr(ExprParser.OrExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#xorExpr}.
	 * @param ctx the parse tree
	 */
	void enterXorExpr(ExprParser.XorExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#xorExpr}.
	 * @param ctx the parse tree
	 */
	void exitXorExpr(ExprParser.XorExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#andExpr}.
	 * @param ctx the parse tree
	 */
	void enterAndExpr(ExprParser.AndExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#andExpr}.
	 * @param ctx the parse tree
	 */
	void exitAndExpr(ExprParser.AndExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#notExpr}.
	 * @param ctx the parse tree
	 */
	void enterNotExpr(ExprParser.NotExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#notExpr}.
	 * @param ctx the parse tree
	 */
	void exitNotExpr(ExprParser.NotExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void enterEqualityExpr(ExprParser.EqualityExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void exitEqualityExpr(ExprParser.EqualityExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#relationExpr}.
	 * @param ctx the parse tree
	 */
	void enterRelationExpr(ExprParser.RelationExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#relationExpr}.
	 * @param ctx the parse tree
	 */
	void exitRelationExpr(ExprParser.RelationExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bitwiseOrExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseOrExpr(ExprParser.BitwiseOrExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bitwiseOrExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseOrExpr(ExprParser.BitwiseOrExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bitwiseXorExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseXorExpr(ExprParser.BitwiseXorExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bitwiseXorExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseXorExpr(ExprParser.BitwiseXorExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bitwiseAndExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseAndExpr(ExprParser.BitwiseAndExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bitwiseAndExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseAndExpr(ExprParser.BitwiseAndExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bitwiseShiftExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseShiftExpr(ExprParser.BitwiseShiftExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bitwiseShiftExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseShiftExpr(ExprParser.BitwiseShiftExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#additiveExpr}.
	 * @param ctx the parse tree
	 */
	void enterAdditiveExpr(ExprParser.AdditiveExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#additiveExpr}.
	 * @param ctx the parse tree
	 */
	void exitAdditiveExpr(ExprParser.AdditiveExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 */
	void enterMultiplicativeExpr(ExprParser.MultiplicativeExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 */
	void exitMultiplicativeExpr(ExprParser.MultiplicativeExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bvConcatExpr}.
	 * @param ctx the parse tree
	 */
	void enterBvConcatExpr(ExprParser.BvConcatExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bvConcatExpr}.
	 * @param ctx the parse tree
	 */
	void exitBvConcatExpr(ExprParser.BvConcatExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bvExtendExpr}.
	 * @param ctx the parse tree
	 */
	void enterBvExtendExpr(ExprParser.BvExtendExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bvExtendExpr}.
	 * @param ctx the parse tree
	 */
	void exitBvExtendExpr(ExprParser.BvExtendExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#unaryExpr}.
	 * @param ctx the parse tree
	 */
	void enterUnaryExpr(ExprParser.UnaryExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#unaryExpr}.
	 * @param ctx the parse tree
	 */
	void exitUnaryExpr(ExprParser.UnaryExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bitwiseNotExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseNotExpr(ExprParser.BitwiseNotExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bitwiseNotExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseNotExpr(ExprParser.BitwiseNotExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#functionCall}.
	 * @param ctx the parse tree
	 */
	void enterFunctionCall(ExprParser.FunctionCallContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#functionCall}.
	 * @param ctx the parse tree
	 */
	void exitFunctionCall(ExprParser.FunctionCallContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#arrayRead}.
	 * @param ctx the parse tree
	 */
	void enterArrayRead(ExprParser.ArrayReadContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#arrayRead}.
	 * @param ctx the parse tree
	 */
	void exitArrayRead(ExprParser.ArrayReadContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#arrayWrite}.
	 * @param ctx the parse tree
	 */
	void enterArrayWrite(ExprParser.ArrayWriteContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#arrayWrite}.
	 * @param ctx the parse tree
	 */
	void exitArrayWrite(ExprParser.ArrayWriteContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#primeExpr}.
	 * @param ctx the parse tree
	 */
	void enterPrimeExpr(ExprParser.PrimeExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#primeExpr}.
	 * @param ctx the parse tree
	 */
	void exitPrimeExpr(ExprParser.PrimeExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bvExtract}.
	 * @param ctx the parse tree
	 */
	void enterBvExtract(ExprParser.BvExtractContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bvExtract}.
	 * @param ctx the parse tree
	 */
	void exitBvExtract(ExprParser.BvExtractContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#primaryExpr}.
	 * @param ctx the parse tree
	 */
	void enterPrimaryExpr(ExprParser.PrimaryExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#primaryExpr}.
	 * @param ctx the parse tree
	 */
	void exitPrimaryExpr(ExprParser.PrimaryExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#trueExpr}.
	 * @param ctx the parse tree
	 */
	void enterTrueExpr(ExprParser.TrueExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#trueExpr}.
	 * @param ctx the parse tree
	 */
	void exitTrueExpr(ExprParser.TrueExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#falseExpr}.
	 * @param ctx the parse tree
	 */
	void enterFalseExpr(ExprParser.FalseExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#falseExpr}.
	 * @param ctx the parse tree
	 */
	void exitFalseExpr(ExprParser.FalseExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#intLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterIntLitExpr(ExprParser.IntLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#intLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitIntLitExpr(ExprParser.IntLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#ratLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterRatLitExpr(ExprParser.RatLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#ratLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitRatLitExpr(ExprParser.RatLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#arrLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterArrLitExpr(ExprParser.ArrLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#arrLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitArrLitExpr(ExprParser.ArrLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bvLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterBvLitExpr(ExprParser.BvLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bvLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitBvLitExpr(ExprParser.BvLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#fpLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterFpLitExpr(ExprParser.FpLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#fpLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitFpLitExpr(ExprParser.FpLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#idExpr}.
	 * @param ctx the parse tree
	 */
	void enterIdExpr(ExprParser.IdExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#idExpr}.
	 * @param ctx the parse tree
	 */
	void exitIdExpr(ExprParser.IdExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void enterParenExpr(ExprParser.ParenExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void exitParenExpr(ExprParser.ParenExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#decl}.
	 * @param ctx the parse tree
	 */
	void enterDecl(ExprParser.DeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#decl}.
	 * @param ctx the parse tree
	 */
	void exitDecl(ExprParser.DeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#declList}.
	 * @param ctx the parse tree
	 */
	void enterDeclList(ExprParser.DeclListContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#declList}.
	 * @param ctx the parse tree
	 */
	void exitDeclList(ExprParser.DeclListContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#type}.
	 * @param ctx the parse tree
	 */
	void enterType(ExprParser.TypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#type}.
	 * @param ctx the parse tree
	 */
	void exitType(ExprParser.TypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#typeList}.
	 * @param ctx the parse tree
	 */
	void enterTypeList(ExprParser.TypeListContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#typeList}.
	 * @param ctx the parse tree
	 */
	void exitTypeList(ExprParser.TypeListContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#boolType}.
	 * @param ctx the parse tree
	 */
	void enterBoolType(ExprParser.BoolTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#boolType}.
	 * @param ctx the parse tree
	 */
	void exitBoolType(ExprParser.BoolTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#intType}.
	 * @param ctx the parse tree
	 */
	void enterIntType(ExprParser.IntTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#intType}.
	 * @param ctx the parse tree
	 */
	void exitIntType(ExprParser.IntTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#ratType}.
	 * @param ctx the parse tree
	 */
	void enterRatType(ExprParser.RatTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#ratType}.
	 * @param ctx the parse tree
	 */
	void exitRatType(ExprParser.RatTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#funcType}.
	 * @param ctx the parse tree
	 */
	void enterFuncType(ExprParser.FuncTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#funcType}.
	 * @param ctx the parse tree
	 */
	void exitFuncType(ExprParser.FuncTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void enterArrayType(ExprParser.ArrayTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void exitArrayType(ExprParser.ArrayTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#bvType}.
	 * @param ctx the parse tree
	 */
	void enterBvType(ExprParser.BvTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#bvType}.
	 * @param ctx the parse tree
	 */
	void exitBvType(ExprParser.BvTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link ExprParser#fpType}.
	 * @param ctx the parse tree
	 */
	void enterFpType(ExprParser.FpTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link ExprParser#fpType}.
	 * @param ctx the parse tree
	 */
	void exitFpType(ExprParser.FpTypeContext ctx);
}