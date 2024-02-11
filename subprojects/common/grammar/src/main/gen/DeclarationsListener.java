// Generated from /home/levente/Documents/University/theta-fresh/subprojects/common/grammar/src/main/antlr/Declarations.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link DeclarationsParser}.
 */
public interface DeclarationsListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#decl}.
	 * @param ctx the parse tree
	 */
	void enterDecl(DeclarationsParser.DeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#decl}.
	 * @param ctx the parse tree
	 */
	void exitDecl(DeclarationsParser.DeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#declList}.
	 * @param ctx the parse tree
	 */
	void enterDeclList(DeclarationsParser.DeclListContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#declList}.
	 * @param ctx the parse tree
	 */
	void exitDeclList(DeclarationsParser.DeclListContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#type}.
	 * @param ctx the parse tree
	 */
	void enterType(DeclarationsParser.TypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#type}.
	 * @param ctx the parse tree
	 */
	void exitType(DeclarationsParser.TypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#typeList}.
	 * @param ctx the parse tree
	 */
	void enterTypeList(DeclarationsParser.TypeListContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#typeList}.
	 * @param ctx the parse tree
	 */
	void exitTypeList(DeclarationsParser.TypeListContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#boolType}.
	 * @param ctx the parse tree
	 */
	void enterBoolType(DeclarationsParser.BoolTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#boolType}.
	 * @param ctx the parse tree
	 */
	void exitBoolType(DeclarationsParser.BoolTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#intType}.
	 * @param ctx the parse tree
	 */
	void enterIntType(DeclarationsParser.IntTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#intType}.
	 * @param ctx the parse tree
	 */
	void exitIntType(DeclarationsParser.IntTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#ratType}.
	 * @param ctx the parse tree
	 */
	void enterRatType(DeclarationsParser.RatTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#ratType}.
	 * @param ctx the parse tree
	 */
	void exitRatType(DeclarationsParser.RatTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#funcType}.
	 * @param ctx the parse tree
	 */
	void enterFuncType(DeclarationsParser.FuncTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#funcType}.
	 * @param ctx the parse tree
	 */
	void exitFuncType(DeclarationsParser.FuncTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void enterArrayType(DeclarationsParser.ArrayTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void exitArrayType(DeclarationsParser.ArrayTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#bvType}.
	 * @param ctx the parse tree
	 */
	void enterBvType(DeclarationsParser.BvTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#bvType}.
	 * @param ctx the parse tree
	 */
	void exitBvType(DeclarationsParser.BvTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link DeclarationsParser#fpType}.
	 * @param ctx the parse tree
	 */
	void enterFpType(DeclarationsParser.FpTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link DeclarationsParser#fpType}.
	 * @param ctx the parse tree
	 */
	void exitFpType(DeclarationsParser.FpTypeContext ctx);
}