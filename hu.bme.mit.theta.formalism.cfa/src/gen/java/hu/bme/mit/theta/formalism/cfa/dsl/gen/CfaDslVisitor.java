// Generated from CfaDsl.g4 by ANTLR 4.5.3
package hu.bme.mit.theta.formalism.cfa.dsl.gen;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link CfaDslParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface CfaDslVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#spec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec(CfaDslParser.SpecContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#varDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarDecl(CfaDslParser.VarDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#procDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProcDecl(CfaDslParser.ProcDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#loc}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLoc(CfaDslParser.LocContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#edge}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEdge(CfaDslParser.EdgeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl(CfaDslParser.DeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#declList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDeclList(CfaDslParser.DeclListContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#type}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitType(CfaDslParser.TypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#typeList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeList(CfaDslParser.TypeListContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#boolType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolType(CfaDslParser.BoolTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#intType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntType(CfaDslParser.IntTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#ratType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatType(CfaDslParser.RatTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#funcType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncType(CfaDslParser.FuncTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#arrayType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayType(CfaDslParser.ArrayTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpr(CfaDslParser.ExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#exprList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExprList(CfaDslParser.ExprListContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#funcLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncLitExpr(CfaDslParser.FuncLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#iteExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIteExpr(CfaDslParser.IteExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#iffExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIffExpr(CfaDslParser.IffExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#implyExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitImplyExpr(CfaDslParser.ImplyExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#quantifiedExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuantifiedExpr(CfaDslParser.QuantifiedExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#forallExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitForallExpr(CfaDslParser.ForallExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#existsExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExistsExpr(CfaDslParser.ExistsExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#orExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOrExpr(CfaDslParser.OrExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#andExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAndExpr(CfaDslParser.AndExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#notExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNotExpr(CfaDslParser.NotExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#equalityExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEqualityExpr(CfaDslParser.EqualityExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#relationExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRelationExpr(CfaDslParser.RelationExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#additiveExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAdditiveExpr(CfaDslParser.AdditiveExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#multiplicativeExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMultiplicativeExpr(CfaDslParser.MultiplicativeExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#negExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNegExpr(CfaDslParser.NegExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#accessorExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAccessorExpr(CfaDslParser.AccessorExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#access}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAccess(CfaDslParser.AccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#funcAccess}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncAccess(CfaDslParser.FuncAccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#arrayAccess}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayAccess(CfaDslParser.ArrayAccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#primeAccess}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrimeAccess(CfaDslParser.PrimeAccessContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#primaryExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrimaryExpr(CfaDslParser.PrimaryExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#trueExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTrueExpr(CfaDslParser.TrueExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#falseExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFalseExpr(CfaDslParser.FalseExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#intLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntLitExpr(CfaDslParser.IntLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#ratLitExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatLitExpr(CfaDslParser.RatLitExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#idExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdExpr(CfaDslParser.IdExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#parenExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenExpr(CfaDslParser.ParenExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#stmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStmt(CfaDslParser.StmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#stmtList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStmtList(CfaDslParser.StmtListContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#assignStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssignStmt(CfaDslParser.AssignStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#havocStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitHavocStmt(CfaDslParser.HavocStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#assumeStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssumeStmt(CfaDslParser.AssumeStmtContext ctx);
	/**
	 * Visit a parse tree produced by {@link CfaDslParser#returnStmt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReturnStmt(CfaDslParser.ReturnStmtContext ctx);
}