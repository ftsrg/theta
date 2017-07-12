// Generated from CfaDsl.g4 by ANTLR 4.5.3
package hu.bme.mit.theta.formalism.cfa.dsl.gen;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link CfaDslParser}.
 */
public interface CfaDslListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#spec}.
	 * @param ctx the parse tree
	 */
	void enterSpec(CfaDslParser.SpecContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#spec}.
	 * @param ctx the parse tree
	 */
	void exitSpec(CfaDslParser.SpecContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#varDecl}.
	 * @param ctx the parse tree
	 */
	void enterVarDecl(CfaDslParser.VarDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#varDecl}.
	 * @param ctx the parse tree
	 */
	void exitVarDecl(CfaDslParser.VarDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#procDecl}.
	 * @param ctx the parse tree
	 */
	void enterProcDecl(CfaDslParser.ProcDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#procDecl}.
	 * @param ctx the parse tree
	 */
	void exitProcDecl(CfaDslParser.ProcDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#loc}.
	 * @param ctx the parse tree
	 */
	void enterLoc(CfaDslParser.LocContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#loc}.
	 * @param ctx the parse tree
	 */
	void exitLoc(CfaDslParser.LocContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#edge}.
	 * @param ctx the parse tree
	 */
	void enterEdge(CfaDslParser.EdgeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#edge}.
	 * @param ctx the parse tree
	 */
	void exitEdge(CfaDslParser.EdgeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#decl}.
	 * @param ctx the parse tree
	 */
	void enterDecl(CfaDslParser.DeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#decl}.
	 * @param ctx the parse tree
	 */
	void exitDecl(CfaDslParser.DeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#declList}.
	 * @param ctx the parse tree
	 */
	void enterDeclList(CfaDslParser.DeclListContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#declList}.
	 * @param ctx the parse tree
	 */
	void exitDeclList(CfaDslParser.DeclListContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#type}.
	 * @param ctx the parse tree
	 */
	void enterType(CfaDslParser.TypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#type}.
	 * @param ctx the parse tree
	 */
	void exitType(CfaDslParser.TypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#typeList}.
	 * @param ctx the parse tree
	 */
	void enterTypeList(CfaDslParser.TypeListContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#typeList}.
	 * @param ctx the parse tree
	 */
	void exitTypeList(CfaDslParser.TypeListContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#boolType}.
	 * @param ctx the parse tree
	 */
	void enterBoolType(CfaDslParser.BoolTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#boolType}.
	 * @param ctx the parse tree
	 */
	void exitBoolType(CfaDslParser.BoolTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#intType}.
	 * @param ctx the parse tree
	 */
	void enterIntType(CfaDslParser.IntTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#intType}.
	 * @param ctx the parse tree
	 */
	void exitIntType(CfaDslParser.IntTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#ratType}.
	 * @param ctx the parse tree
	 */
	void enterRatType(CfaDslParser.RatTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#ratType}.
	 * @param ctx the parse tree
	 */
	void exitRatType(CfaDslParser.RatTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#funcType}.
	 * @param ctx the parse tree
	 */
	void enterFuncType(CfaDslParser.FuncTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#funcType}.
	 * @param ctx the parse tree
	 */
	void exitFuncType(CfaDslParser.FuncTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void enterArrayType(CfaDslParser.ArrayTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void exitArrayType(CfaDslParser.ArrayTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#expr}.
	 * @param ctx the parse tree
	 */
	void enterExpr(CfaDslParser.ExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#expr}.
	 * @param ctx the parse tree
	 */
	void exitExpr(CfaDslParser.ExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#exprList}.
	 * @param ctx the parse tree
	 */
	void enterExprList(CfaDslParser.ExprListContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#exprList}.
	 * @param ctx the parse tree
	 */
	void exitExprList(CfaDslParser.ExprListContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#funcLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterFuncLitExpr(CfaDslParser.FuncLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#funcLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitFuncLitExpr(CfaDslParser.FuncLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#iteExpr}.
	 * @param ctx the parse tree
	 */
	void enterIteExpr(CfaDslParser.IteExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#iteExpr}.
	 * @param ctx the parse tree
	 */
	void exitIteExpr(CfaDslParser.IteExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#iffExpr}.
	 * @param ctx the parse tree
	 */
	void enterIffExpr(CfaDslParser.IffExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#iffExpr}.
	 * @param ctx the parse tree
	 */
	void exitIffExpr(CfaDslParser.IffExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#implyExpr}.
	 * @param ctx the parse tree
	 */
	void enterImplyExpr(CfaDslParser.ImplyExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#implyExpr}.
	 * @param ctx the parse tree
	 */
	void exitImplyExpr(CfaDslParser.ImplyExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 */
	void enterQuantifiedExpr(CfaDslParser.QuantifiedExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 */
	void exitQuantifiedExpr(CfaDslParser.QuantifiedExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#forallExpr}.
	 * @param ctx the parse tree
	 */
	void enterForallExpr(CfaDslParser.ForallExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#forallExpr}.
	 * @param ctx the parse tree
	 */
	void exitForallExpr(CfaDslParser.ForallExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#existsExpr}.
	 * @param ctx the parse tree
	 */
	void enterExistsExpr(CfaDslParser.ExistsExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#existsExpr}.
	 * @param ctx the parse tree
	 */
	void exitExistsExpr(CfaDslParser.ExistsExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#orExpr}.
	 * @param ctx the parse tree
	 */
	void enterOrExpr(CfaDslParser.OrExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#orExpr}.
	 * @param ctx the parse tree
	 */
	void exitOrExpr(CfaDslParser.OrExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#andExpr}.
	 * @param ctx the parse tree
	 */
	void enterAndExpr(CfaDslParser.AndExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#andExpr}.
	 * @param ctx the parse tree
	 */
	void exitAndExpr(CfaDslParser.AndExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#notExpr}.
	 * @param ctx the parse tree
	 */
	void enterNotExpr(CfaDslParser.NotExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#notExpr}.
	 * @param ctx the parse tree
	 */
	void exitNotExpr(CfaDslParser.NotExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void enterEqualityExpr(CfaDslParser.EqualityExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void exitEqualityExpr(CfaDslParser.EqualityExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#relationExpr}.
	 * @param ctx the parse tree
	 */
	void enterRelationExpr(CfaDslParser.RelationExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#relationExpr}.
	 * @param ctx the parse tree
	 */
	void exitRelationExpr(CfaDslParser.RelationExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#additiveExpr}.
	 * @param ctx the parse tree
	 */
	void enterAdditiveExpr(CfaDslParser.AdditiveExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#additiveExpr}.
	 * @param ctx the parse tree
	 */
	void exitAdditiveExpr(CfaDslParser.AdditiveExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 */
	void enterMultiplicativeExpr(CfaDslParser.MultiplicativeExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 */
	void exitMultiplicativeExpr(CfaDslParser.MultiplicativeExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#negExpr}.
	 * @param ctx the parse tree
	 */
	void enterNegExpr(CfaDslParser.NegExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#negExpr}.
	 * @param ctx the parse tree
	 */
	void exitNegExpr(CfaDslParser.NegExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#accessorExpr}.
	 * @param ctx the parse tree
	 */
	void enterAccessorExpr(CfaDslParser.AccessorExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#accessorExpr}.
	 * @param ctx the parse tree
	 */
	void exitAccessorExpr(CfaDslParser.AccessorExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#access}.
	 * @param ctx the parse tree
	 */
	void enterAccess(CfaDslParser.AccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#access}.
	 * @param ctx the parse tree
	 */
	void exitAccess(CfaDslParser.AccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#funcAccess}.
	 * @param ctx the parse tree
	 */
	void enterFuncAccess(CfaDslParser.FuncAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#funcAccess}.
	 * @param ctx the parse tree
	 */
	void exitFuncAccess(CfaDslParser.FuncAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#arrayAccess}.
	 * @param ctx the parse tree
	 */
	void enterArrayAccess(CfaDslParser.ArrayAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#arrayAccess}.
	 * @param ctx the parse tree
	 */
	void exitArrayAccess(CfaDslParser.ArrayAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#primeAccess}.
	 * @param ctx the parse tree
	 */
	void enterPrimeAccess(CfaDslParser.PrimeAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#primeAccess}.
	 * @param ctx the parse tree
	 */
	void exitPrimeAccess(CfaDslParser.PrimeAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#primaryExpr}.
	 * @param ctx the parse tree
	 */
	void enterPrimaryExpr(CfaDslParser.PrimaryExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#primaryExpr}.
	 * @param ctx the parse tree
	 */
	void exitPrimaryExpr(CfaDslParser.PrimaryExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#trueExpr}.
	 * @param ctx the parse tree
	 */
	void enterTrueExpr(CfaDslParser.TrueExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#trueExpr}.
	 * @param ctx the parse tree
	 */
	void exitTrueExpr(CfaDslParser.TrueExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#falseExpr}.
	 * @param ctx the parse tree
	 */
	void enterFalseExpr(CfaDslParser.FalseExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#falseExpr}.
	 * @param ctx the parse tree
	 */
	void exitFalseExpr(CfaDslParser.FalseExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#intLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterIntLitExpr(CfaDslParser.IntLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#intLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitIntLitExpr(CfaDslParser.IntLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#ratLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterRatLitExpr(CfaDslParser.RatLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#ratLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitRatLitExpr(CfaDslParser.RatLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#idExpr}.
	 * @param ctx the parse tree
	 */
	void enterIdExpr(CfaDslParser.IdExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#idExpr}.
	 * @param ctx the parse tree
	 */
	void exitIdExpr(CfaDslParser.IdExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void enterParenExpr(CfaDslParser.ParenExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void exitParenExpr(CfaDslParser.ParenExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterStmt(CfaDslParser.StmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitStmt(CfaDslParser.StmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#stmtList}.
	 * @param ctx the parse tree
	 */
	void enterStmtList(CfaDslParser.StmtListContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#stmtList}.
	 * @param ctx the parse tree
	 */
	void exitStmtList(CfaDslParser.StmtListContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#assignStmt}.
	 * @param ctx the parse tree
	 */
	void enterAssignStmt(CfaDslParser.AssignStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#assignStmt}.
	 * @param ctx the parse tree
	 */
	void exitAssignStmt(CfaDslParser.AssignStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#havocStmt}.
	 * @param ctx the parse tree
	 */
	void enterHavocStmt(CfaDslParser.HavocStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#havocStmt}.
	 * @param ctx the parse tree
	 */
	void exitHavocStmt(CfaDslParser.HavocStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#assumeStmt}.
	 * @param ctx the parse tree
	 */
	void enterAssumeStmt(CfaDslParser.AssumeStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#assumeStmt}.
	 * @param ctx the parse tree
	 */
	void exitAssumeStmt(CfaDslParser.AssumeStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link CfaDslParser#returnStmt}.
	 * @param ctx the parse tree
	 */
	void enterReturnStmt(CfaDslParser.ReturnStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link CfaDslParser#returnStmt}.
	 * @param ctx the parse tree
	 */
	void exitReturnStmt(CfaDslParser.ReturnStmtContext ctx);
}