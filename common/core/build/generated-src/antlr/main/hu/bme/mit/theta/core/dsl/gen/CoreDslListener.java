// Generated from CoreDsl.g4 by ANTLR 4.7.2
package hu.bme.mit.theta.core.dsl.gen;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link CoreDslParser}.
 */
public interface CoreDslListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#decl}.
	 * @param ctx the parse tree
	 */
	void enterDecl(CoreDslParser.DeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#decl}.
	 * @param ctx the parse tree
	 */
	void exitDecl(CoreDslParser.DeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#declList}.
	 * @param ctx the parse tree
	 */
	void enterDeclList(CoreDslParser.DeclListContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#declList}.
	 * @param ctx the parse tree
	 */
	void exitDeclList(CoreDslParser.DeclListContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#type}.
	 * @param ctx the parse tree
	 */
	void enterType(CoreDslParser.TypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#type}.
	 * @param ctx the parse tree
	 */
	void exitType(CoreDslParser.TypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#typeList}.
	 * @param ctx the parse tree
	 */
	void enterTypeList(CoreDslParser.TypeListContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#typeList}.
	 * @param ctx the parse tree
	 */
	void exitTypeList(CoreDslParser.TypeListContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#boolType}.
	 * @param ctx the parse tree
	 */
	void enterBoolType(CoreDslParser.BoolTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#boolType}.
	 * @param ctx the parse tree
	 */
	void exitBoolType(CoreDslParser.BoolTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#intType}.
	 * @param ctx the parse tree
	 */
	void enterIntType(CoreDslParser.IntTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#intType}.
	 * @param ctx the parse tree
	 */
	void exitIntType(CoreDslParser.IntTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#ratType}.
	 * @param ctx the parse tree
	 */
	void enterRatType(CoreDslParser.RatTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#ratType}.
	 * @param ctx the parse tree
	 */
	void exitRatType(CoreDslParser.RatTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#funcType}.
	 * @param ctx the parse tree
	 */
	void enterFuncType(CoreDslParser.FuncTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#funcType}.
	 * @param ctx the parse tree
	 */
	void exitFuncType(CoreDslParser.FuncTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void enterArrayType(CoreDslParser.ArrayTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void exitArrayType(CoreDslParser.ArrayTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bvType}.
	 * @param ctx the parse tree
	 */
	void enterBvType(CoreDslParser.BvTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bvType}.
	 * @param ctx the parse tree
	 */
	void exitBvType(CoreDslParser.BvTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#expr}.
	 * @param ctx the parse tree
	 */
	void enterExpr(CoreDslParser.ExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#expr}.
	 * @param ctx the parse tree
	 */
	void exitExpr(CoreDslParser.ExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#exprList}.
	 * @param ctx the parse tree
	 */
	void enterExprList(CoreDslParser.ExprListContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#exprList}.
	 * @param ctx the parse tree
	 */
	void exitExprList(CoreDslParser.ExprListContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#funcLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterFuncLitExpr(CoreDslParser.FuncLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#funcLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitFuncLitExpr(CoreDslParser.FuncLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#iteExpr}.
	 * @param ctx the parse tree
	 */
	void enterIteExpr(CoreDslParser.IteExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#iteExpr}.
	 * @param ctx the parse tree
	 */
	void exitIteExpr(CoreDslParser.IteExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#iffExpr}.
	 * @param ctx the parse tree
	 */
	void enterIffExpr(CoreDslParser.IffExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#iffExpr}.
	 * @param ctx the parse tree
	 */
	void exitIffExpr(CoreDslParser.IffExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#implyExpr}.
	 * @param ctx the parse tree
	 */
	void enterImplyExpr(CoreDslParser.ImplyExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#implyExpr}.
	 * @param ctx the parse tree
	 */
	void exitImplyExpr(CoreDslParser.ImplyExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 */
	void enterQuantifiedExpr(CoreDslParser.QuantifiedExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 */
	void exitQuantifiedExpr(CoreDslParser.QuantifiedExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#forallExpr}.
	 * @param ctx the parse tree
	 */
	void enterForallExpr(CoreDslParser.ForallExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#forallExpr}.
	 * @param ctx the parse tree
	 */
	void exitForallExpr(CoreDslParser.ForallExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#existsExpr}.
	 * @param ctx the parse tree
	 */
	void enterExistsExpr(CoreDslParser.ExistsExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#existsExpr}.
	 * @param ctx the parse tree
	 */
	void exitExistsExpr(CoreDslParser.ExistsExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#orExpr}.
	 * @param ctx the parse tree
	 */
	void enterOrExpr(CoreDslParser.OrExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#orExpr}.
	 * @param ctx the parse tree
	 */
	void exitOrExpr(CoreDslParser.OrExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#andExpr}.
	 * @param ctx the parse tree
	 */
	void enterAndExpr(CoreDslParser.AndExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#andExpr}.
	 * @param ctx the parse tree
	 */
	void exitAndExpr(CoreDslParser.AndExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#notExpr}.
	 * @param ctx the parse tree
	 */
	void enterNotExpr(CoreDslParser.NotExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#notExpr}.
	 * @param ctx the parse tree
	 */
	void exitNotExpr(CoreDslParser.NotExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void enterEqualityExpr(CoreDslParser.EqualityExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void exitEqualityExpr(CoreDslParser.EqualityExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#relationExpr}.
	 * @param ctx the parse tree
	 */
	void enterRelationExpr(CoreDslParser.RelationExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#relationExpr}.
	 * @param ctx the parse tree
	 */
	void exitRelationExpr(CoreDslParser.RelationExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bitwiseOrExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseOrExpr(CoreDslParser.BitwiseOrExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bitwiseOrExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseOrExpr(CoreDslParser.BitwiseOrExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bitwiseXorExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseXorExpr(CoreDslParser.BitwiseXorExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bitwiseXorExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseXorExpr(CoreDslParser.BitwiseXorExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bitwiseAndExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseAndExpr(CoreDslParser.BitwiseAndExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bitwiseAndExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseAndExpr(CoreDslParser.BitwiseAndExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bitwiseShiftExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseShiftExpr(CoreDslParser.BitwiseShiftExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bitwiseShiftExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseShiftExpr(CoreDslParser.BitwiseShiftExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#additiveExpr}.
	 * @param ctx the parse tree
	 */
	void enterAdditiveExpr(CoreDslParser.AdditiveExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#additiveExpr}.
	 * @param ctx the parse tree
	 */
	void exitAdditiveExpr(CoreDslParser.AdditiveExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 */
	void enterMultiplicativeExpr(CoreDslParser.MultiplicativeExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 */
	void exitMultiplicativeExpr(CoreDslParser.MultiplicativeExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bvConcatExpr}.
	 * @param ctx the parse tree
	 */
	void enterBvConcatExpr(CoreDslParser.BvConcatExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bvConcatExpr}.
	 * @param ctx the parse tree
	 */
	void exitBvConcatExpr(CoreDslParser.BvConcatExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bvExtendExpr}.
	 * @param ctx the parse tree
	 */
	void enterBvExtendExpr(CoreDslParser.BvExtendExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bvExtendExpr}.
	 * @param ctx the parse tree
	 */
	void exitBvExtendExpr(CoreDslParser.BvExtendExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#unaryExpr}.
	 * @param ctx the parse tree
	 */
	void enterUnaryExpr(CoreDslParser.UnaryExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#unaryExpr}.
	 * @param ctx the parse tree
	 */
	void exitUnaryExpr(CoreDslParser.UnaryExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bitwiseNotExpr}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseNotExpr(CoreDslParser.BitwiseNotExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bitwiseNotExpr}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseNotExpr(CoreDslParser.BitwiseNotExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#accessorExpr}.
	 * @param ctx the parse tree
	 */
	void enterAccessorExpr(CoreDslParser.AccessorExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#accessorExpr}.
	 * @param ctx the parse tree
	 */
	void exitAccessorExpr(CoreDslParser.AccessorExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#access}.
	 * @param ctx the parse tree
	 */
	void enterAccess(CoreDslParser.AccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#access}.
	 * @param ctx the parse tree
	 */
	void exitAccess(CoreDslParser.AccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#funcAccess}.
	 * @param ctx the parse tree
	 */
	void enterFuncAccess(CoreDslParser.FuncAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#funcAccess}.
	 * @param ctx the parse tree
	 */
	void exitFuncAccess(CoreDslParser.FuncAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#arrayAccess}.
	 * @param ctx the parse tree
	 */
	void enterArrayAccess(CoreDslParser.ArrayAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#arrayAccess}.
	 * @param ctx the parse tree
	 */
	void exitArrayAccess(CoreDslParser.ArrayAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#primeAccess}.
	 * @param ctx the parse tree
	 */
	void enterPrimeAccess(CoreDslParser.PrimeAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#primeAccess}.
	 * @param ctx the parse tree
	 */
	void exitPrimeAccess(CoreDslParser.PrimeAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bvExtractAccess}.
	 * @param ctx the parse tree
	 */
	void enterBvExtractAccess(CoreDslParser.BvExtractAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bvExtractAccess}.
	 * @param ctx the parse tree
	 */
	void exitBvExtractAccess(CoreDslParser.BvExtractAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#primaryExpr}.
	 * @param ctx the parse tree
	 */
	void enterPrimaryExpr(CoreDslParser.PrimaryExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#primaryExpr}.
	 * @param ctx the parse tree
	 */
	void exitPrimaryExpr(CoreDslParser.PrimaryExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#trueExpr}.
	 * @param ctx the parse tree
	 */
	void enterTrueExpr(CoreDslParser.TrueExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#trueExpr}.
	 * @param ctx the parse tree
	 */
	void exitTrueExpr(CoreDslParser.TrueExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#falseExpr}.
	 * @param ctx the parse tree
	 */
	void enterFalseExpr(CoreDslParser.FalseExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#falseExpr}.
	 * @param ctx the parse tree
	 */
	void exitFalseExpr(CoreDslParser.FalseExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#intLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterIntLitExpr(CoreDslParser.IntLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#intLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitIntLitExpr(CoreDslParser.IntLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#ratLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterRatLitExpr(CoreDslParser.RatLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#ratLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitRatLitExpr(CoreDslParser.RatLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#bvLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterBvLitExpr(CoreDslParser.BvLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#bvLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitBvLitExpr(CoreDslParser.BvLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#idExpr}.
	 * @param ctx the parse tree
	 */
	void enterIdExpr(CoreDslParser.IdExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#idExpr}.
	 * @param ctx the parse tree
	 */
	void exitIdExpr(CoreDslParser.IdExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void enterParenExpr(CoreDslParser.ParenExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void exitParenExpr(CoreDslParser.ParenExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterStmt(CoreDslParser.StmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitStmt(CoreDslParser.StmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#stmtList}.
	 * @param ctx the parse tree
	 */
	void enterStmtList(CoreDslParser.StmtListContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#stmtList}.
	 * @param ctx the parse tree
	 */
	void exitStmtList(CoreDslParser.StmtListContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#assignStmt}.
	 * @param ctx the parse tree
	 */
	void enterAssignStmt(CoreDslParser.AssignStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#assignStmt}.
	 * @param ctx the parse tree
	 */
	void exitAssignStmt(CoreDslParser.AssignStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#havocStmt}.
	 * @param ctx the parse tree
	 */
	void enterHavocStmt(CoreDslParser.HavocStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#havocStmt}.
	 * @param ctx the parse tree
	 */
	void exitHavocStmt(CoreDslParser.HavocStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link CoreDslParser#assumeStmt}.
	 * @param ctx the parse tree
	 */
	void enterAssumeStmt(CoreDslParser.AssumeStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link CoreDslParser#assumeStmt}.
	 * @param ctx the parse tree
	 */
	void exitAssumeStmt(CoreDslParser.AssumeStmtContext ctx);
}