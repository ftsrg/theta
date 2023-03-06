// Generated from /home/solarowl/Repositories/theta/subprojects/xcfa/litmus2xcfa/src/main/antlr/LitmusAssertions.g4 by ANTLR 4.10.1
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link LitmusAssertionsParser}.
 */
public interface LitmusAssertionsListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link LitmusAssertionsParser#assertionFilter}.
	 * @param ctx the parse tree
	 */
	void enterAssertionFilter(LitmusAssertionsParser.AssertionFilterContext ctx);
	/**
	 * Exit a parse tree produced by {@link LitmusAssertionsParser#assertionFilter}.
	 * @param ctx the parse tree
	 */
	void exitAssertionFilter(LitmusAssertionsParser.AssertionFilterContext ctx);
	/**
	 * Enter a parse tree produced by {@link LitmusAssertionsParser#assertionList}.
	 * @param ctx the parse tree
	 */
	void enterAssertionList(LitmusAssertionsParser.AssertionListContext ctx);
	/**
	 * Exit a parse tree produced by {@link LitmusAssertionsParser#assertionList}.
	 * @param ctx the parse tree
	 */
	void exitAssertionList(LitmusAssertionsParser.AssertionListContext ctx);
	/**
	 * Enter a parse tree produced by the {@code assertionBasic}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void enterAssertionBasic(LitmusAssertionsParser.AssertionBasicContext ctx);
	/**
	 * Exit a parse tree produced by the {@code assertionBasic}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void exitAssertionBasic(LitmusAssertionsParser.AssertionBasicContext ctx);
	/**
	 * Enter a parse tree produced by the {@code assertionAnd}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void enterAssertionAnd(LitmusAssertionsParser.AssertionAndContext ctx);
	/**
	 * Exit a parse tree produced by the {@code assertionAnd}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void exitAssertionAnd(LitmusAssertionsParser.AssertionAndContext ctx);
	/**
	 * Enter a parse tree produced by the {@code assertionOr}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void enterAssertionOr(LitmusAssertionsParser.AssertionOrContext ctx);
	/**
	 * Exit a parse tree produced by the {@code assertionOr}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void exitAssertionOr(LitmusAssertionsParser.AssertionOrContext ctx);
	/**
	 * Enter a parse tree produced by the {@code assertionParenthesis}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void enterAssertionParenthesis(LitmusAssertionsParser.AssertionParenthesisContext ctx);
	/**
	 * Exit a parse tree produced by the {@code assertionParenthesis}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void exitAssertionParenthesis(LitmusAssertionsParser.AssertionParenthesisContext ctx);
	/**
	 * Enter a parse tree produced by the {@code assertionNot}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void enterAssertionNot(LitmusAssertionsParser.AssertionNotContext ctx);
	/**
	 * Exit a parse tree produced by the {@code assertionNot}
	 * labeled alternative in {@link LitmusAssertionsParser#assertion}.
	 * @param ctx the parse tree
	 */
	void exitAssertionNot(LitmusAssertionsParser.AssertionNotContext ctx);
	/**
	 * Enter a parse tree produced by {@link LitmusAssertionsParser#assertionValue}.
	 * @param ctx the parse tree
	 */
	void enterAssertionValue(LitmusAssertionsParser.AssertionValueContext ctx);
	/**
	 * Exit a parse tree produced by {@link LitmusAssertionsParser#assertionValue}.
	 * @param ctx the parse tree
	 */
	void exitAssertionValue(LitmusAssertionsParser.AssertionValueContext ctx);
	/**
	 * Enter a parse tree produced by {@link LitmusAssertionsParser#varName}.
	 * @param ctx the parse tree
	 */
	void enterVarName(LitmusAssertionsParser.VarNameContext ctx);
	/**
	 * Exit a parse tree produced by {@link LitmusAssertionsParser#varName}.
	 * @param ctx the parse tree
	 */
	void exitVarName(LitmusAssertionsParser.VarNameContext ctx);
	/**
	 * Enter a parse tree produced by {@link LitmusAssertionsParser#constant}.
	 * @param ctx the parse tree
	 */
	void enterConstant(LitmusAssertionsParser.ConstantContext ctx);
	/**
	 * Exit a parse tree produced by {@link LitmusAssertionsParser#constant}.
	 * @param ctx the parse tree
	 */
	void exitConstant(LitmusAssertionsParser.ConstantContext ctx);
	/**
	 * Enter a parse tree produced by {@link LitmusAssertionsParser#assertionListExpectationList}.
	 * @param ctx the parse tree
	 */
	void enterAssertionListExpectationList(LitmusAssertionsParser.AssertionListExpectationListContext ctx);
	/**
	 * Exit a parse tree produced by {@link LitmusAssertionsParser#assertionListExpectationList}.
	 * @param ctx the parse tree
	 */
	void exitAssertionListExpectationList(LitmusAssertionsParser.AssertionListExpectationListContext ctx);
	/**
	 * Enter a parse tree produced by {@link LitmusAssertionsParser#assertionListExpectation}.
	 * @param ctx the parse tree
	 */
	void enterAssertionListExpectation(LitmusAssertionsParser.AssertionListExpectationContext ctx);
	/**
	 * Exit a parse tree produced by {@link LitmusAssertionsParser#assertionListExpectation}.
	 * @param ctx the parse tree
	 */
	void exitAssertionListExpectation(LitmusAssertionsParser.AssertionListExpectationContext ctx);
	/**
	 * Enter a parse tree produced by the {@code eqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void enterEqCompare(LitmusAssertionsParser.EqCompareContext ctx);
	/**
	 * Exit a parse tree produced by the {@code eqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void exitEqCompare(LitmusAssertionsParser.EqCompareContext ctx);
	/**
	 * Enter a parse tree produced by the {@code neqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void enterNeqCompare(LitmusAssertionsParser.NeqCompareContext ctx);
	/**
	 * Exit a parse tree produced by the {@code neqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void exitNeqCompare(LitmusAssertionsParser.NeqCompareContext ctx);
	/**
	 * Enter a parse tree produced by the {@code geqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void enterGeqCompare(LitmusAssertionsParser.GeqCompareContext ctx);
	/**
	 * Exit a parse tree produced by the {@code geqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void exitGeqCompare(LitmusAssertionsParser.GeqCompareContext ctx);
	/**
	 * Enter a parse tree produced by the {@code leqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void enterLeqCompare(LitmusAssertionsParser.LeqCompareContext ctx);
	/**
	 * Exit a parse tree produced by the {@code leqCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void exitLeqCompare(LitmusAssertionsParser.LeqCompareContext ctx);
	/**
	 * Enter a parse tree produced by the {@code ltCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void enterLtCompare(LitmusAssertionsParser.LtCompareContext ctx);
	/**
	 * Exit a parse tree produced by the {@code ltCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void exitLtCompare(LitmusAssertionsParser.LtCompareContext ctx);
	/**
	 * Enter a parse tree produced by the {@code gtCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void enterGtCompare(LitmusAssertionsParser.GtCompareContext ctx);
	/**
	 * Exit a parse tree produced by the {@code gtCompare}
	 * labeled alternative in {@link LitmusAssertionsParser#assertionCompare}.
	 * @param ctx the parse tree
	 */
	void exitGtCompare(LitmusAssertionsParser.GtCompareContext ctx);
	/**
	 * Enter a parse tree produced by {@link LitmusAssertionsParser#threadId}.
	 * @param ctx the parse tree
	 */
	void enterThreadId(LitmusAssertionsParser.ThreadIdContext ctx);
	/**
	 * Exit a parse tree produced by {@link LitmusAssertionsParser#threadId}.
	 * @param ctx the parse tree
	 */
	void exitThreadId(LitmusAssertionsParser.ThreadIdContext ctx);
}