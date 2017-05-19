// Generated from TcfaDsl.g4 by ANTLR 4.5.3
package hu.bme.mit.theta.formalism.tcfa.dsl.gen;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link TcfaDslParser}.
 */
public interface TcfaDslListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#tcfaSpec}.
	 * @param ctx the parse tree
	 */
	void enterTcfaSpec(TcfaDslParser.TcfaSpecContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#tcfaSpec}.
	 * @param ctx the parse tree
	 */
	void exitTcfaSpec(TcfaDslParser.TcfaSpecContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#constDecl}.
	 * @param ctx the parse tree
	 */
	void enterConstDecl(TcfaDslParser.ConstDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#constDecl}.
	 * @param ctx the parse tree
	 */
	void exitConstDecl(TcfaDslParser.ConstDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#varDecl}.
	 * @param ctx the parse tree
	 */
	void enterVarDecl(TcfaDslParser.VarDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#varDecl}.
	 * @param ctx the parse tree
	 */
	void exitVarDecl(TcfaDslParser.VarDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#tcfaParamDecl}.
	 * @param ctx the parse tree
	 */
	void enterTcfaParamDecl(TcfaDslParser.TcfaParamDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#tcfaParamDecl}.
	 * @param ctx the parse tree
	 */
	void exitTcfaParamDecl(TcfaDslParser.TcfaParamDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#tcfaParamDeclList}.
	 * @param ctx the parse tree
	 */
	void enterTcfaParamDeclList(TcfaDslParser.TcfaParamDeclListContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#tcfaParamDeclList}.
	 * @param ctx the parse tree
	 */
	void exitTcfaParamDeclList(TcfaDslParser.TcfaParamDeclListContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#tcfaDecl}.
	 * @param ctx the parse tree
	 */
	void enterTcfaDecl(TcfaDslParser.TcfaDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#tcfaDecl}.
	 * @param ctx the parse tree
	 */
	void exitTcfaDecl(TcfaDslParser.TcfaDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#tcfa}.
	 * @param ctx the parse tree
	 */
	void enterTcfa(TcfaDslParser.TcfaContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#tcfa}.
	 * @param ctx the parse tree
	 */
	void exitTcfa(TcfaDslParser.TcfaContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#prodTcfa}.
	 * @param ctx the parse tree
	 */
	void enterProdTcfa(TcfaDslParser.ProdTcfaContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#prodTcfa}.
	 * @param ctx the parse tree
	 */
	void exitProdTcfa(TcfaDslParser.ProdTcfaContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#primaryTcfa}.
	 * @param ctx the parse tree
	 */
	void enterPrimaryTcfa(TcfaDslParser.PrimaryTcfaContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#primaryTcfa}.
	 * @param ctx the parse tree
	 */
	void exitPrimaryTcfa(TcfaDslParser.PrimaryTcfaContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#defTcfa}.
	 * @param ctx the parse tree
	 */
	void enterDefTcfa(TcfaDslParser.DefTcfaContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#defTcfa}.
	 * @param ctx the parse tree
	 */
	void exitDefTcfa(TcfaDslParser.DefTcfaContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#loc}.
	 * @param ctx the parse tree
	 */
	void enterLoc(TcfaDslParser.LocContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#loc}.
	 * @param ctx the parse tree
	 */
	void exitLoc(TcfaDslParser.LocContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#edge}.
	 * @param ctx the parse tree
	 */
	void enterEdge(TcfaDslParser.EdgeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#edge}.
	 * @param ctx the parse tree
	 */
	void exitEdge(TcfaDslParser.EdgeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#refTcfa}.
	 * @param ctx the parse tree
	 */
	void enterRefTcfa(TcfaDslParser.RefTcfaContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#refTcfa}.
	 * @param ctx the parse tree
	 */
	void exitRefTcfa(TcfaDslParser.RefTcfaContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#parenTcfa}.
	 * @param ctx the parse tree
	 */
	void enterParenTcfa(TcfaDslParser.ParenTcfaContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#parenTcfa}.
	 * @param ctx the parse tree
	 */
	void exitParenTcfa(TcfaDslParser.ParenTcfaContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#decl}.
	 * @param ctx the parse tree
	 */
	void enterDecl(TcfaDslParser.DeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#decl}.
	 * @param ctx the parse tree
	 */
	void exitDecl(TcfaDslParser.DeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#declList}.
	 * @param ctx the parse tree
	 */
	void enterDeclList(TcfaDslParser.DeclListContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#declList}.
	 * @param ctx the parse tree
	 */
	void exitDeclList(TcfaDslParser.DeclListContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#type}.
	 * @param ctx the parse tree
	 */
	void enterType(TcfaDslParser.TypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#type}.
	 * @param ctx the parse tree
	 */
	void exitType(TcfaDslParser.TypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#typeList}.
	 * @param ctx the parse tree
	 */
	void enterTypeList(TcfaDslParser.TypeListContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#typeList}.
	 * @param ctx the parse tree
	 */
	void exitTypeList(TcfaDslParser.TypeListContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#boolType}.
	 * @param ctx the parse tree
	 */
	void enterBoolType(TcfaDslParser.BoolTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#boolType}.
	 * @param ctx the parse tree
	 */
	void exitBoolType(TcfaDslParser.BoolTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#intType}.
	 * @param ctx the parse tree
	 */
	void enterIntType(TcfaDslParser.IntTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#intType}.
	 * @param ctx the parse tree
	 */
	void exitIntType(TcfaDslParser.IntTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#ratType}.
	 * @param ctx the parse tree
	 */
	void enterRatType(TcfaDslParser.RatTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#ratType}.
	 * @param ctx the parse tree
	 */
	void exitRatType(TcfaDslParser.RatTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#clockType}.
	 * @param ctx the parse tree
	 */
	void enterClockType(TcfaDslParser.ClockTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#clockType}.
	 * @param ctx the parse tree
	 */
	void exitClockType(TcfaDslParser.ClockTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#funcType}.
	 * @param ctx the parse tree
	 */
	void enterFuncType(TcfaDslParser.FuncTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#funcType}.
	 * @param ctx the parse tree
	 */
	void exitFuncType(TcfaDslParser.FuncTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void enterArrayType(TcfaDslParser.ArrayTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void exitArrayType(TcfaDslParser.ArrayTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#expr}.
	 * @param ctx the parse tree
	 */
	void enterExpr(TcfaDslParser.ExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#expr}.
	 * @param ctx the parse tree
	 */
	void exitExpr(TcfaDslParser.ExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#exprList}.
	 * @param ctx the parse tree
	 */
	void enterExprList(TcfaDslParser.ExprListContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#exprList}.
	 * @param ctx the parse tree
	 */
	void exitExprList(TcfaDslParser.ExprListContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#funcLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterFuncLitExpr(TcfaDslParser.FuncLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#funcLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitFuncLitExpr(TcfaDslParser.FuncLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#iteExpr}.
	 * @param ctx the parse tree
	 */
	void enterIteExpr(TcfaDslParser.IteExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#iteExpr}.
	 * @param ctx the parse tree
	 */
	void exitIteExpr(TcfaDslParser.IteExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#iffExpr}.
	 * @param ctx the parse tree
	 */
	void enterIffExpr(TcfaDslParser.IffExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#iffExpr}.
	 * @param ctx the parse tree
	 */
	void exitIffExpr(TcfaDslParser.IffExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#implyExpr}.
	 * @param ctx the parse tree
	 */
	void enterImplyExpr(TcfaDslParser.ImplyExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#implyExpr}.
	 * @param ctx the parse tree
	 */
	void exitImplyExpr(TcfaDslParser.ImplyExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 */
	void enterQuantifiedExpr(TcfaDslParser.QuantifiedExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 */
	void exitQuantifiedExpr(TcfaDslParser.QuantifiedExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#forallExpr}.
	 * @param ctx the parse tree
	 */
	void enterForallExpr(TcfaDslParser.ForallExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#forallExpr}.
	 * @param ctx the parse tree
	 */
	void exitForallExpr(TcfaDslParser.ForallExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#existsExpr}.
	 * @param ctx the parse tree
	 */
	void enterExistsExpr(TcfaDslParser.ExistsExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#existsExpr}.
	 * @param ctx the parse tree
	 */
	void exitExistsExpr(TcfaDslParser.ExistsExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#orExpr}.
	 * @param ctx the parse tree
	 */
	void enterOrExpr(TcfaDslParser.OrExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#orExpr}.
	 * @param ctx the parse tree
	 */
	void exitOrExpr(TcfaDslParser.OrExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#andExpr}.
	 * @param ctx the parse tree
	 */
	void enterAndExpr(TcfaDslParser.AndExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#andExpr}.
	 * @param ctx the parse tree
	 */
	void exitAndExpr(TcfaDslParser.AndExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#notExpr}.
	 * @param ctx the parse tree
	 */
	void enterNotExpr(TcfaDslParser.NotExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#notExpr}.
	 * @param ctx the parse tree
	 */
	void exitNotExpr(TcfaDslParser.NotExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void enterEqualityExpr(TcfaDslParser.EqualityExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void exitEqualityExpr(TcfaDslParser.EqualityExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#relationExpr}.
	 * @param ctx the parse tree
	 */
	void enterRelationExpr(TcfaDslParser.RelationExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#relationExpr}.
	 * @param ctx the parse tree
	 */
	void exitRelationExpr(TcfaDslParser.RelationExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#additiveExpr}.
	 * @param ctx the parse tree
	 */
	void enterAdditiveExpr(TcfaDslParser.AdditiveExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#additiveExpr}.
	 * @param ctx the parse tree
	 */
	void exitAdditiveExpr(TcfaDslParser.AdditiveExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 */
	void enterMultiplicativeExpr(TcfaDslParser.MultiplicativeExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 */
	void exitMultiplicativeExpr(TcfaDslParser.MultiplicativeExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#negExpr}.
	 * @param ctx the parse tree
	 */
	void enterNegExpr(TcfaDslParser.NegExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#negExpr}.
	 * @param ctx the parse tree
	 */
	void exitNegExpr(TcfaDslParser.NegExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#accessorExpr}.
	 * @param ctx the parse tree
	 */
	void enterAccessorExpr(TcfaDslParser.AccessorExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#accessorExpr}.
	 * @param ctx the parse tree
	 */
	void exitAccessorExpr(TcfaDslParser.AccessorExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#access}.
	 * @param ctx the parse tree
	 */
	void enterAccess(TcfaDslParser.AccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#access}.
	 * @param ctx the parse tree
	 */
	void exitAccess(TcfaDslParser.AccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#funcAccess}.
	 * @param ctx the parse tree
	 */
	void enterFuncAccess(TcfaDslParser.FuncAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#funcAccess}.
	 * @param ctx the parse tree
	 */
	void exitFuncAccess(TcfaDslParser.FuncAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#arrayAccess}.
	 * @param ctx the parse tree
	 */
	void enterArrayAccess(TcfaDslParser.ArrayAccessContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#arrayAccess}.
	 * @param ctx the parse tree
	 */
	void exitArrayAccess(TcfaDslParser.ArrayAccessContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#primaryExpr}.
	 * @param ctx the parse tree
	 */
	void enterPrimaryExpr(TcfaDslParser.PrimaryExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#primaryExpr}.
	 * @param ctx the parse tree
	 */
	void exitPrimaryExpr(TcfaDslParser.PrimaryExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#trueExpr}.
	 * @param ctx the parse tree
	 */
	void enterTrueExpr(TcfaDslParser.TrueExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#trueExpr}.
	 * @param ctx the parse tree
	 */
	void exitTrueExpr(TcfaDslParser.TrueExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#falseExpr}.
	 * @param ctx the parse tree
	 */
	void enterFalseExpr(TcfaDslParser.FalseExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#falseExpr}.
	 * @param ctx the parse tree
	 */
	void exitFalseExpr(TcfaDslParser.FalseExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#intLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterIntLitExpr(TcfaDslParser.IntLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#intLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitIntLitExpr(TcfaDslParser.IntLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#ratLitExpr}.
	 * @param ctx the parse tree
	 */
	void enterRatLitExpr(TcfaDslParser.RatLitExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#ratLitExpr}.
	 * @param ctx the parse tree
	 */
	void exitRatLitExpr(TcfaDslParser.RatLitExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#idExpr}.
	 * @param ctx the parse tree
	 */
	void enterIdExpr(TcfaDslParser.IdExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#idExpr}.
	 * @param ctx the parse tree
	 */
	void exitIdExpr(TcfaDslParser.IdExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void enterParenExpr(TcfaDslParser.ParenExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void exitParenExpr(TcfaDslParser.ParenExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterStmt(TcfaDslParser.StmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitStmt(TcfaDslParser.StmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#stmtList}.
	 * @param ctx the parse tree
	 */
	void enterStmtList(TcfaDslParser.StmtListContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#stmtList}.
	 * @param ctx the parse tree
	 */
	void exitStmtList(TcfaDslParser.StmtListContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#assignStmt}.
	 * @param ctx the parse tree
	 */
	void enterAssignStmt(TcfaDslParser.AssignStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#assignStmt}.
	 * @param ctx the parse tree
	 */
	void exitAssignStmt(TcfaDslParser.AssignStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#havocStmt}.
	 * @param ctx the parse tree
	 */
	void enterHavocStmt(TcfaDslParser.HavocStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#havocStmt}.
	 * @param ctx the parse tree
	 */
	void exitHavocStmt(TcfaDslParser.HavocStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link TcfaDslParser#assumeStmt}.
	 * @param ctx the parse tree
	 */
	void enterAssumeStmt(TcfaDslParser.AssumeStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link TcfaDslParser#assumeStmt}.
	 * @param ctx the parse tree
	 */
	void exitAssumeStmt(TcfaDslParser.AssumeStmtContext ctx);
}