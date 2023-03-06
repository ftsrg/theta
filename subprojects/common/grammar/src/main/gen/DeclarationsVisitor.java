// Generated from /home/solarowl/Repositories/theta/subprojects/common/grammar/src/main/antlr/Declarations.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link DeclarationsParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface DeclarationsVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#decl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDecl(DeclarationsParser.DeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#declList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDeclList(DeclarationsParser.DeclListContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#type}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitType(DeclarationsParser.TypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#typeList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeList(DeclarationsParser.TypeListContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#boolType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolType(DeclarationsParser.BoolTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#intType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntType(DeclarationsParser.IntTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#ratType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRatType(DeclarationsParser.RatTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#funcType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFuncType(DeclarationsParser.FuncTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#arrayType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayType(DeclarationsParser.ArrayTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#bvType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvType(DeclarationsParser.BvTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link DeclarationsParser#fpType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFpType(DeclarationsParser.FpTypeContext ctx);
}