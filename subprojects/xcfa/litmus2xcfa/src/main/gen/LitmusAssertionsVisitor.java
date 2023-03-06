// Generated from /home/solarowl/Repositories/theta/subprojects/xcfa/litmus2xcfa/src/main/antlr/LitmusAssertions.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link LitmusAssertionsParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface LitmusAssertionsVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link LitmusAssertionsParser#assertionFilter}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionFilter(LitmusAssertionsParser.AssertionFilterContext ctx);
	/**
	 * Visit a parse tree produced by {@link LitmusAssertionsParser#assertionList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionList(LitmusAssertionsParser.AssertionListContext ctx);
	/**
	 * Visit a parse tree produced by the {@code assertionBasic}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionBasic(LitmusAssertionsParser.AssertionBasicContext ctx);
	/**
	 * Visit a parse tree produced by the {@code assertionAnd}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionAnd(LitmusAssertionsParser.AssertionAndContext ctx);
	/**
	 * Visit a parse tree produced by the {@code assertionOr}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionOr(LitmusAssertionsParser.AssertionOrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code assertionParenthesis}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionParenthesis(LitmusAssertionsParser.AssertionParenthesisContext ctx);
	/**
	 * Visit a parse tree produced by the {@code assertionNot}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionNot(LitmusAssertionsParser.AssertionNotContext ctx);
	/**
	 * Visit a parse tree produced by {@link LitmusAssertionsParser#assertionValue}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionValue(LitmusAssertionsParser.AssertionValueContext ctx);
	/**
	 * Visit a parse tree produced by {@link LitmusAssertionsParser#varName}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarName(LitmusAssertionsParser.VarNameContext ctx);
	/**
	 * Visit a parse tree produced by {@link LitmusAssertionsParser#constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstant(LitmusAssertionsParser.ConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link LitmusAssertionsParser#assertionListExpectationList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionListExpectationList(LitmusAssertionsParser.AssertionListExpectationListContext ctx);
	/**
	 * Visit a parse tree produced by {@link LitmusAssertionsParser#assertionListExpectation}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssertionListExpectation(LitmusAssertionsParser.AssertionListExpectationContext ctx);
	/**
	 * Visit a parse tree produced by the {@code eqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEqCompare(LitmusAssertionsParser.EqCompareContext ctx);
	/**
	 * Visit a parse tree produced by the {@code neqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNeqCompare(LitmusAssertionsParser.NeqCompareContext ctx);
	/**
	 * Visit a parse tree produced by the {@code geqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeqCompare(LitmusAssertionsParser.GeqCompareContext ctx);
	/**
	 * Visit a parse tree produced by the {@code leqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLeqCompare(LitmusAssertionsParser.LeqCompareContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ltCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLtCompare(LitmusAssertionsParser.LtCompareContext ctx);
	/**
	 * Visit a parse tree produced by the {@code gtCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGtCompare(LitmusAssertionsParser.GtCompareContext ctx);
	/**
	 * Visit a parse tree produced by {@link LitmusAssertionsParser#threadId}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitThreadId(LitmusAssertionsParser.ThreadIdContext ctx);
}