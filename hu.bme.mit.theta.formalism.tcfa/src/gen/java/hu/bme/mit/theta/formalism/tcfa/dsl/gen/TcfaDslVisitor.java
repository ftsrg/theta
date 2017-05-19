// Generated from TcfaDsl.g4 by ANTLR 4.5.3
package hu.bme.mit.theta.formalism.tcfa.dsl.gen;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link TcfaDslParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface TcfaDslVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#tcfaSpec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTcfaSpec(TcfaDslParser.TcfaSpecContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#constDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstDecl(TcfaDslParser.ConstDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#varDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarDecl(TcfaDslParser.VarDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#tcfaParamDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTcfaParamDecl(TcfaDslParser.TcfaParamDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#tcfaParamDeclList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTcfaParamDeclList(TcfaDslParser.TcfaParamDeclListContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#tcfaDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTcfaDecl(TcfaDslParser.TcfaDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#tcfa}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTcfa(TcfaDslParser.TcfaContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#prodTcfa}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProdTcfa(TcfaDslParser.ProdTcfaContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#primaryTcfa}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrimaryTcfa(TcfaDslParser.PrimaryTcfaContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#defTcfa}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDefTcfa(TcfaDslParser.DefTcfaContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#loc}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLoc(TcfaDslParser.LocContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#edge}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEdge(TcfaDslParser.EdgeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#refTcfa}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRefTcfa(TcfaDslParser.RefTcfaContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#parenTcfa}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenTcfa(TcfaDslParser.ParenTcfaContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl(TcfaDslParser.DeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#declList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDeclList(TcfaDslParser.DeclListContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#type}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitType(TcfaDslParser.TypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#typeList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeList(TcfaDslParser.TypeListContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#boolType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolType(TcfaDslParser.BoolTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#intType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntType(TcfaDslParser.IntTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#ratType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatType(TcfaDslParser.RatTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#clockType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitClockType(TcfaDslParser.ClockTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#funcType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncType(TcfaDslParser.FuncTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#arrayType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayType(TcfaDslParser.ArrayTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpr(TcfaDslParser.ExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#exprList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExprList(TcfaDslParser.ExprListContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#funcLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncLitExpr(TcfaDslParser.FuncLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#iteExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIteExpr(TcfaDslParser.IteExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#iffExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIffExpr(TcfaDslParser.IffExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#implyExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitImplyExpr(TcfaDslParser.ImplyExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuantifiedExpr(TcfaDslParser.QuantifiedExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#forallExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitForallExpr(TcfaDslParser.ForallExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#existsExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExistsExpr(TcfaDslParser.ExistsExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#orExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOrExpr(TcfaDslParser.OrExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#andExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAndExpr(TcfaDslParser.AndExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#notExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNotExpr(TcfaDslParser.NotExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#equalityExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEqualityExpr(TcfaDslParser.EqualityExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#relationExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRelationExpr(TcfaDslParser.RelationExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#additiveExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAdditiveExpr(TcfaDslParser.AdditiveExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMultiplicativeExpr(TcfaDslParser.MultiplicativeExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#negExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNegExpr(TcfaDslParser.NegExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#accessorExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAccessorExpr(TcfaDslParser.AccessorExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#access}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAccess(TcfaDslParser.AccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#funcAccess}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncAccess(TcfaDslParser.FuncAccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#arrayAccess}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayAccess(TcfaDslParser.ArrayAccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#primaryExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrimaryExpr(TcfaDslParser.PrimaryExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#trueExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTrueExpr(TcfaDslParser.TrueExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#falseExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFalseExpr(TcfaDslParser.FalseExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#intLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntLitExpr(TcfaDslParser.IntLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#ratLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatLitExpr(TcfaDslParser.RatLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#idExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdExpr(TcfaDslParser.IdExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#parenExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenExpr(TcfaDslParser.ParenExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStmt(TcfaDslParser.StmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#stmtList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStmtList(TcfaDslParser.StmtListContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#assignStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssignStmt(TcfaDslParser.AssignStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#havocStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitHavocStmt(TcfaDslParser.HavocStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link TcfaDslParser#assumeStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssumeStmt(TcfaDslParser.AssumeStmtContext ctx);
}