// Generated from /home/levente/Documents/University/theta-fresh/subprojects/common/grammar/src/main/antlr/Type.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link TypeParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface TypeVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link TypeParser#type}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitType(TypeParser.TypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TypeParser#typeList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeList(TypeParser.TypeListContext ctx);
	/**
	 * Visit a parse tree produced by {@link TypeParser#boolType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolType(TypeParser.BoolTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TypeParser#intType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntType(TypeParser.IntTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TypeParser#ratType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatType(TypeParser.RatTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TypeParser#funcType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncType(TypeParser.FuncTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TypeParser#arrayType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayType(TypeParser.ArrayTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TypeParser#bvType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvType(TypeParser.BvTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link TypeParser#fpType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFpType(TypeParser.FpTypeContext ctx);
}