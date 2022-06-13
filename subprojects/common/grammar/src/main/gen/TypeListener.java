// Generated from /home/levente/Documents/University/theta-fresh/subprojects/common/grammar/src/main/antlr/Type.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link TypeParser}.
 */
public interface TypeListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link TypeParser#type}.
	 * @param ctx the parse tree
	 */
	void enterType(TypeParser.TypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypeParser#type}.
	 * @param ctx the parse tree
	 */
	void exitType(TypeParser.TypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypeParser#typeList}.
	 * @param ctx the parse tree
	 */
	void enterTypeList(TypeParser.TypeListContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypeParser#typeList}.
	 * @param ctx the parse tree
	 */
	void exitTypeList(TypeParser.TypeListContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypeParser#boolType}.
	 * @param ctx the parse tree
	 */
	void enterBoolType(TypeParser.BoolTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypeParser#boolType}.
	 * @param ctx the parse tree
	 */
	void exitBoolType(TypeParser.BoolTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypeParser#intType}.
	 * @param ctx the parse tree
	 */
	void enterIntType(TypeParser.IntTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypeParser#intType}.
	 * @param ctx the parse tree
	 */
	void exitIntType(TypeParser.IntTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypeParser#ratType}.
	 * @param ctx the parse tree
	 */
	void enterRatType(TypeParser.RatTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypeParser#ratType}.
	 * @param ctx the parse tree
	 */
	void exitRatType(TypeParser.RatTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypeParser#funcType}.
	 * @param ctx the parse tree
	 */
	void enterFuncType(TypeParser.FuncTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypeParser#funcType}.
	 * @param ctx the parse tree
	 */
	void exitFuncType(TypeParser.FuncTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypeParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void enterArrayType(TypeParser.ArrayTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypeParser#arrayType}.
	 * @param ctx the parse tree
	 */
	void exitArrayType(TypeParser.ArrayTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypeParser#bvType}.
	 * @param ctx the parse tree
	 */
	void enterBvType(TypeParser.BvTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypeParser#bvType}.
	 * @param ctx the parse tree
	 */
	void exitBvType(TypeParser.BvTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link TypeParser#fpType}.
	 * @param ctx the parse tree
	 */
	void enterFpType(TypeParser.FpTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link TypeParser#fpType}.
	 * @param ctx the parse tree
	 */
	void exitFpType(TypeParser.FpTypeContext ctx);
}