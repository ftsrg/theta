// Generated from XtaDsl.g4 by ANTLR 4.7.2
package hu.bme.mit.theta.xta.dsl.gen;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link XtaDslParser}.
 */
public interface XtaDslListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#xta}.
	 * @param ctx the parse tree
	 */
	void enterXta(XtaDslParser.XtaContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#xta}.
	 * @param ctx the parse tree
	 */
	void exitXta(XtaDslParser.XtaContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#iteratorDecl}.
	 * @param ctx the parse tree
	 */
	void enterIteratorDecl(XtaDslParser.IteratorDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#iteratorDecl}.
	 * @param ctx the parse tree
	 */
	void exitIteratorDecl(XtaDslParser.IteratorDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#instantiation}.
	 * @param ctx the parse tree
	 */
	void enterInstantiation(XtaDslParser.InstantiationContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#instantiation}.
	 * @param ctx the parse tree
	 */
	void exitInstantiation(XtaDslParser.InstantiationContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#system}.
	 * @param ctx the parse tree
	 */
	void enterSystem(XtaDslParser.SystemContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#system}.
	 * @param ctx the parse tree
	 */
	void exitSystem(XtaDslParser.SystemContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#parameterList}.
	 * @param ctx the parse tree
	 */
	void enterParameterList(XtaDslParser.ParameterListContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#parameterList}.
	 * @param ctx the parse tree
	 */
	void exitParameterList(XtaDslParser.ParameterListContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#parameterDecl}.
	 * @param ctx the parse tree
	 */
	void enterParameterDecl(XtaDslParser.ParameterDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#parameterDecl}.
	 * @param ctx the parse tree
	 */
	void exitParameterDecl(XtaDslParser.ParameterDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#parameterId}.
	 * @param ctx the parse tree
	 */
	void enterParameterId(XtaDslParser.ParameterIdContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#parameterId}.
	 * @param ctx the parse tree
	 */
	void exitParameterId(XtaDslParser.ParameterIdContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#functionDecl}.
	 * @param ctx the parse tree
	 */
	void enterFunctionDecl(XtaDslParser.FunctionDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#functionDecl}.
	 * @param ctx the parse tree
	 */
	void exitFunctionDecl(XtaDslParser.FunctionDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#processDecl}.
	 * @param ctx the parse tree
	 */
	void enterProcessDecl(XtaDslParser.ProcessDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#processDecl}.
	 * @param ctx the parse tree
	 */
	void exitProcessDecl(XtaDslParser.ProcessDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#processBody}.
	 * @param ctx the parse tree
	 */
	void enterProcessBody(XtaDslParser.ProcessBodyContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#processBody}.
	 * @param ctx the parse tree
	 */
	void exitProcessBody(XtaDslParser.ProcessBodyContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#states}.
	 * @param ctx the parse tree
	 */
	void enterStates(XtaDslParser.StatesContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#states}.
	 * @param ctx the parse tree
	 */
	void exitStates(XtaDslParser.StatesContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#stateDecl}.
	 * @param ctx the parse tree
	 */
	void enterStateDecl(XtaDslParser.StateDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#stateDecl}.
	 * @param ctx the parse tree
	 */
	void exitStateDecl(XtaDslParser.StateDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#commit}.
	 * @param ctx the parse tree
	 */
	void enterCommit(XtaDslParser.CommitContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#commit}.
	 * @param ctx the parse tree
	 */
	void exitCommit(XtaDslParser.CommitContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#urgent}.
	 * @param ctx the parse tree
	 */
	void enterUrgent(XtaDslParser.UrgentContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#urgent}.
	 * @param ctx the parse tree
	 */
	void exitUrgent(XtaDslParser.UrgentContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#stateList}.
	 * @param ctx the parse tree
	 */
	void enterStateList(XtaDslParser.StateListContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#stateList}.
	 * @param ctx the parse tree
	 */
	void exitStateList(XtaDslParser.StateListContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#init}.
	 * @param ctx the parse tree
	 */
	void enterInit(XtaDslParser.InitContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#init}.
	 * @param ctx the parse tree
	 */
	void exitInit(XtaDslParser.InitContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#transitions}.
	 * @param ctx the parse tree
	 */
	void enterTransitions(XtaDslParser.TransitionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#transitions}.
	 * @param ctx the parse tree
	 */
	void exitTransitions(XtaDslParser.TransitionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#transition}.
	 * @param ctx the parse tree
	 */
	void enterTransition(XtaDslParser.TransitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#transition}.
	 * @param ctx the parse tree
	 */
	void exitTransition(XtaDslParser.TransitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#transitionOpt}.
	 * @param ctx the parse tree
	 */
	void enterTransitionOpt(XtaDslParser.TransitionOptContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#transitionOpt}.
	 * @param ctx the parse tree
	 */
	void exitTransitionOpt(XtaDslParser.TransitionOptContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#transitionBody}.
	 * @param ctx the parse tree
	 */
	void enterTransitionBody(XtaDslParser.TransitionBodyContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#transitionBody}.
	 * @param ctx the parse tree
	 */
	void exitTransitionBody(XtaDslParser.TransitionBodyContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#select}.
	 * @param ctx the parse tree
	 */
	void enterSelect(XtaDslParser.SelectContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#select}.
	 * @param ctx the parse tree
	 */
	void exitSelect(XtaDslParser.SelectContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#guard}.
	 * @param ctx the parse tree
	 */
	void enterGuard(XtaDslParser.GuardContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#guard}.
	 * @param ctx the parse tree
	 */
	void exitGuard(XtaDslParser.GuardContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#sync}.
	 * @param ctx the parse tree
	 */
	void enterSync(XtaDslParser.SyncContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#sync}.
	 * @param ctx the parse tree
	 */
	void exitSync(XtaDslParser.SyncContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#assign}.
	 * @param ctx the parse tree
	 */
	void enterAssign(XtaDslParser.AssignContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#assign}.
	 * @param ctx the parse tree
	 */
	void exitAssign(XtaDslParser.AssignContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#typeDecl}.
	 * @param ctx the parse tree
	 */
	void enterTypeDecl(XtaDslParser.TypeDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#typeDecl}.
	 * @param ctx the parse tree
	 */
	void exitTypeDecl(XtaDslParser.TypeDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#arrayId}.
	 * @param ctx the parse tree
	 */
	void enterArrayId(XtaDslParser.ArrayIdContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#arrayId}.
	 * @param ctx the parse tree
	 */
	void exitArrayId(XtaDslParser.ArrayIdContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#arrayIndex}.
	 * @param ctx the parse tree
	 */
	void enterArrayIndex(XtaDslParser.ArrayIndexContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#arrayIndex}.
	 * @param ctx the parse tree
	 */
	void exitArrayIndex(XtaDslParser.ArrayIndexContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#idIndex}.
	 * @param ctx the parse tree
	 */
	void enterIdIndex(XtaDslParser.IdIndexContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#idIndex}.
	 * @param ctx the parse tree
	 */
	void exitIdIndex(XtaDslParser.IdIndexContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#expressionIndex}.
	 * @param ctx the parse tree
	 */
	void enterExpressionIndex(XtaDslParser.ExpressionIndexContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#expressionIndex}.
	 * @param ctx the parse tree
	 */
	void exitExpressionIndex(XtaDslParser.ExpressionIndexContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#type}.
	 * @param ctx the parse tree
	 */
	void enterType(XtaDslParser.TypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#type}.
	 * @param ctx the parse tree
	 */
	void exitType(XtaDslParser.TypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#typePrefix}.
	 * @param ctx the parse tree
	 */
	void enterTypePrefix(XtaDslParser.TypePrefixContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#typePrefix}.
	 * @param ctx the parse tree
	 */
	void exitTypePrefix(XtaDslParser.TypePrefixContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#basicType}.
	 * @param ctx the parse tree
	 */
	void enterBasicType(XtaDslParser.BasicTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#basicType}.
	 * @param ctx the parse tree
	 */
	void exitBasicType(XtaDslParser.BasicTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#refType}.
	 * @param ctx the parse tree
	 */
	void enterRefType(XtaDslParser.RefTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#refType}.
	 * @param ctx the parse tree
	 */
	void exitRefType(XtaDslParser.RefTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#voidType}.
	 * @param ctx the parse tree
	 */
	void enterVoidType(XtaDslParser.VoidTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#voidType}.
	 * @param ctx the parse tree
	 */
	void exitVoidType(XtaDslParser.VoidTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#intType}.
	 * @param ctx the parse tree
	 */
	void enterIntType(XtaDslParser.IntTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#intType}.
	 * @param ctx the parse tree
	 */
	void exitIntType(XtaDslParser.IntTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#clockType}.
	 * @param ctx the parse tree
	 */
	void enterClockType(XtaDslParser.ClockTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#clockType}.
	 * @param ctx the parse tree
	 */
	void exitClockType(XtaDslParser.ClockTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#chanType}.
	 * @param ctx the parse tree
	 */
	void enterChanType(XtaDslParser.ChanTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#chanType}.
	 * @param ctx the parse tree
	 */
	void exitChanType(XtaDslParser.ChanTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#boolType}.
	 * @param ctx the parse tree
	 */
	void enterBoolType(XtaDslParser.BoolTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#boolType}.
	 * @param ctx the parse tree
	 */
	void exitBoolType(XtaDslParser.BoolTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#rangeType}.
	 * @param ctx the parse tree
	 */
	void enterRangeType(XtaDslParser.RangeTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#rangeType}.
	 * @param ctx the parse tree
	 */
	void exitRangeType(XtaDslParser.RangeTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#scalarType}.
	 * @param ctx the parse tree
	 */
	void enterScalarType(XtaDslParser.ScalarTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#scalarType}.
	 * @param ctx the parse tree
	 */
	void exitScalarType(XtaDslParser.ScalarTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#structType}.
	 * @param ctx the parse tree
	 */
	void enterStructType(XtaDslParser.StructTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#structType}.
	 * @param ctx the parse tree
	 */
	void exitStructType(XtaDslParser.StructTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#fieldDecl}.
	 * @param ctx the parse tree
	 */
	void enterFieldDecl(XtaDslParser.FieldDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#fieldDecl}.
	 * @param ctx the parse tree
	 */
	void exitFieldDecl(XtaDslParser.FieldDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#variableDecl}.
	 * @param ctx the parse tree
	 */
	void enterVariableDecl(XtaDslParser.VariableDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#variableDecl}.
	 * @param ctx the parse tree
	 */
	void exitVariableDecl(XtaDslParser.VariableDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#variableId}.
	 * @param ctx the parse tree
	 */
	void enterVariableId(XtaDslParser.VariableIdContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#variableId}.
	 * @param ctx the parse tree
	 */
	void exitVariableId(XtaDslParser.VariableIdContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#initialiser}.
	 * @param ctx the parse tree
	 */
	void enterInitialiser(XtaDslParser.InitialiserContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#initialiser}.
	 * @param ctx the parse tree
	 */
	void exitInitialiser(XtaDslParser.InitialiserContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#simpleInitialiser}.
	 * @param ctx the parse tree
	 */
	void enterSimpleInitialiser(XtaDslParser.SimpleInitialiserContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#simpleInitialiser}.
	 * @param ctx the parse tree
	 */
	void exitSimpleInitialiser(XtaDslParser.SimpleInitialiserContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#compoundInitialiser}.
	 * @param ctx the parse tree
	 */
	void enterCompoundInitialiser(XtaDslParser.CompoundInitialiserContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#compoundInitialiser}.
	 * @param ctx the parse tree
	 */
	void exitCompoundInitialiser(XtaDslParser.CompoundInitialiserContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#block}.
	 * @param ctx the parse tree
	 */
	void enterBlock(XtaDslParser.BlockContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#block}.
	 * @param ctx the parse tree
	 */
	void exitBlock(XtaDslParser.BlockContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#statement}.
	 * @param ctx the parse tree
	 */
	void enterStatement(XtaDslParser.StatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#statement}.
	 * @param ctx the parse tree
	 */
	void exitStatement(XtaDslParser.StatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#skipStatement}.
	 * @param ctx the parse tree
	 */
	void enterSkipStatement(XtaDslParser.SkipStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#skipStatement}.
	 * @param ctx the parse tree
	 */
	void exitSkipStatement(XtaDslParser.SkipStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#expressionStatement}.
	 * @param ctx the parse tree
	 */
	void enterExpressionStatement(XtaDslParser.ExpressionStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#expressionStatement}.
	 * @param ctx the parse tree
	 */
	void exitExpressionStatement(XtaDslParser.ExpressionStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#forStatement}.
	 * @param ctx the parse tree
	 */
	void enterForStatement(XtaDslParser.ForStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#forStatement}.
	 * @param ctx the parse tree
	 */
	void exitForStatement(XtaDslParser.ForStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#foreachStatement}.
	 * @param ctx the parse tree
	 */
	void enterForeachStatement(XtaDslParser.ForeachStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#foreachStatement}.
	 * @param ctx the parse tree
	 */
	void exitForeachStatement(XtaDslParser.ForeachStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#whileStatement}.
	 * @param ctx the parse tree
	 */
	void enterWhileStatement(XtaDslParser.WhileStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#whileStatement}.
	 * @param ctx the parse tree
	 */
	void exitWhileStatement(XtaDslParser.WhileStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#doStatement}.
	 * @param ctx the parse tree
	 */
	void enterDoStatement(XtaDslParser.DoStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#doStatement}.
	 * @param ctx the parse tree
	 */
	void exitDoStatement(XtaDslParser.DoStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#ifStatement}.
	 * @param ctx the parse tree
	 */
	void enterIfStatement(XtaDslParser.IfStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#ifStatement}.
	 * @param ctx the parse tree
	 */
	void exitIfStatement(XtaDslParser.IfStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#returnStatement}.
	 * @param ctx the parse tree
	 */
	void enterReturnStatement(XtaDslParser.ReturnStatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#returnStatement}.
	 * @param ctx the parse tree
	 */
	void exitReturnStatement(XtaDslParser.ReturnStatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#expression}.
	 * @param ctx the parse tree
	 */
	void enterExpression(XtaDslParser.ExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#expression}.
	 * @param ctx the parse tree
	 */
	void exitExpression(XtaDslParser.ExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#quantifiedExpression}.
	 * @param ctx the parse tree
	 */
	void enterQuantifiedExpression(XtaDslParser.QuantifiedExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#quantifiedExpression}.
	 * @param ctx the parse tree
	 */
	void exitQuantifiedExpression(XtaDslParser.QuantifiedExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#forallExpression}.
	 * @param ctx the parse tree
	 */
	void enterForallExpression(XtaDslParser.ForallExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#forallExpression}.
	 * @param ctx the parse tree
	 */
	void exitForallExpression(XtaDslParser.ForallExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#existsExpression}.
	 * @param ctx the parse tree
	 */
	void enterExistsExpression(XtaDslParser.ExistsExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#existsExpression}.
	 * @param ctx the parse tree
	 */
	void exitExistsExpression(XtaDslParser.ExistsExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#textOrImplyExpression}.
	 * @param ctx the parse tree
	 */
	void enterTextOrImplyExpression(XtaDslParser.TextOrImplyExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#textOrImplyExpression}.
	 * @param ctx the parse tree
	 */
	void exitTextOrImplyExpression(XtaDslParser.TextOrImplyExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#textAndExpression}.
	 * @param ctx the parse tree
	 */
	void enterTextAndExpression(XtaDslParser.TextAndExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#textAndExpression}.
	 * @param ctx the parse tree
	 */
	void exitTextAndExpression(XtaDslParser.TextAndExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#textNotExpression}.
	 * @param ctx the parse tree
	 */
	void enterTextNotExpression(XtaDslParser.TextNotExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#textNotExpression}.
	 * @param ctx the parse tree
	 */
	void exitTextNotExpression(XtaDslParser.TextNotExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#assignmentExpression}.
	 * @param ctx the parse tree
	 */
	void enterAssignmentExpression(XtaDslParser.AssignmentExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#assignmentExpression}.
	 * @param ctx the parse tree
	 */
	void exitAssignmentExpression(XtaDslParser.AssignmentExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#conditionalExpression}.
	 * @param ctx the parse tree
	 */
	void enterConditionalExpression(XtaDslParser.ConditionalExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#conditionalExpression}.
	 * @param ctx the parse tree
	 */
	void exitConditionalExpression(XtaDslParser.ConditionalExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#logicalOrExpression}.
	 * @param ctx the parse tree
	 */
	void enterLogicalOrExpression(XtaDslParser.LogicalOrExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#logicalOrExpression}.
	 * @param ctx the parse tree
	 */
	void exitLogicalOrExpression(XtaDslParser.LogicalOrExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#logicalAndExpression}.
	 * @param ctx the parse tree
	 */
	void enterLogicalAndExpression(XtaDslParser.LogicalAndExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#logicalAndExpression}.
	 * @param ctx the parse tree
	 */
	void exitLogicalAndExpression(XtaDslParser.LogicalAndExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bitwiseOrExpression}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseOrExpression(XtaDslParser.BitwiseOrExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bitwiseOrExpression}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseOrExpression(XtaDslParser.BitwiseOrExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bitwiseXorExpression}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseXorExpression(XtaDslParser.BitwiseXorExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bitwiseXorExpression}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseXorExpression(XtaDslParser.BitwiseXorExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bitwiseAndExpression}.
	 * @param ctx the parse tree
	 */
	void enterBitwiseAndExpression(XtaDslParser.BitwiseAndExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bitwiseAndExpression}.
	 * @param ctx the parse tree
	 */
	void exitBitwiseAndExpression(XtaDslParser.BitwiseAndExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#equalityExpression}.
	 * @param ctx the parse tree
	 */
	void enterEqualityExpression(XtaDslParser.EqualityExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#equalityExpression}.
	 * @param ctx the parse tree
	 */
	void exitEqualityExpression(XtaDslParser.EqualityExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#relationalExpression}.
	 * @param ctx the parse tree
	 */
	void enterRelationalExpression(XtaDslParser.RelationalExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#relationalExpression}.
	 * @param ctx the parse tree
	 */
	void exitRelationalExpression(XtaDslParser.RelationalExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#shiftExpression}.
	 * @param ctx the parse tree
	 */
	void enterShiftExpression(XtaDslParser.ShiftExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#shiftExpression}.
	 * @param ctx the parse tree
	 */
	void exitShiftExpression(XtaDslParser.ShiftExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#additiveExpression}.
	 * @param ctx the parse tree
	 */
	void enterAdditiveExpression(XtaDslParser.AdditiveExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#additiveExpression}.
	 * @param ctx the parse tree
	 */
	void exitAdditiveExpression(XtaDslParser.AdditiveExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#multiplicativeExpression}.
	 * @param ctx the parse tree
	 */
	void enterMultiplicativeExpression(XtaDslParser.MultiplicativeExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#multiplicativeExpression}.
	 * @param ctx the parse tree
	 */
	void exitMultiplicativeExpression(XtaDslParser.MultiplicativeExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#prefixExpression}.
	 * @param ctx the parse tree
	 */
	void enterPrefixExpression(XtaDslParser.PrefixExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#prefixExpression}.
	 * @param ctx the parse tree
	 */
	void exitPrefixExpression(XtaDslParser.PrefixExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#postfixExpression}.
	 * @param ctx the parse tree
	 */
	void enterPostfixExpression(XtaDslParser.PostfixExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#postfixExpression}.
	 * @param ctx the parse tree
	 */
	void exitPostfixExpression(XtaDslParser.PostfixExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#primaryExpression}.
	 * @param ctx the parse tree
	 */
	void enterPrimaryExpression(XtaDslParser.PrimaryExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#primaryExpression}.
	 * @param ctx the parse tree
	 */
	void exitPrimaryExpression(XtaDslParser.PrimaryExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#trueExpression}.
	 * @param ctx the parse tree
	 */
	void enterTrueExpression(XtaDslParser.TrueExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#trueExpression}.
	 * @param ctx the parse tree
	 */
	void exitTrueExpression(XtaDslParser.TrueExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#falseExpression}.
	 * @param ctx the parse tree
	 */
	void enterFalseExpression(XtaDslParser.FalseExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#falseExpression}.
	 * @param ctx the parse tree
	 */
	void exitFalseExpression(XtaDslParser.FalseExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#natExpression}.
	 * @param ctx the parse tree
	 */
	void enterNatExpression(XtaDslParser.NatExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#natExpression}.
	 * @param ctx the parse tree
	 */
	void exitNatExpression(XtaDslParser.NatExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#idExpression}.
	 * @param ctx the parse tree
	 */
	void enterIdExpression(XtaDslParser.IdExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#idExpression}.
	 * @param ctx the parse tree
	 */
	void exitIdExpression(XtaDslParser.IdExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#parenthesisExpression}.
	 * @param ctx the parse tree
	 */
	void enterParenthesisExpression(XtaDslParser.ParenthesisExpressionContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#parenthesisExpression}.
	 * @param ctx the parse tree
	 */
	void exitParenthesisExpression(XtaDslParser.ParenthesisExpressionContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#argList}.
	 * @param ctx the parse tree
	 */
	void enterArgList(XtaDslParser.ArgListContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#argList}.
	 * @param ctx the parse tree
	 */
	void exitArgList(XtaDslParser.ArgListContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#textOrImplyOp}.
	 * @param ctx the parse tree
	 */
	void enterTextOrImplyOp(XtaDslParser.TextOrImplyOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#textOrImplyOp}.
	 * @param ctx the parse tree
	 */
	void exitTextOrImplyOp(XtaDslParser.TextOrImplyOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#textOrOp}.
	 * @param ctx the parse tree
	 */
	void enterTextOrOp(XtaDslParser.TextOrOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#textOrOp}.
	 * @param ctx the parse tree
	 */
	void exitTextOrOp(XtaDslParser.TextOrOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#textImplyOp}.
	 * @param ctx the parse tree
	 */
	void enterTextImplyOp(XtaDslParser.TextImplyOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#textImplyOp}.
	 * @param ctx the parse tree
	 */
	void exitTextImplyOp(XtaDslParser.TextImplyOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#textAndOp}.
	 * @param ctx the parse tree
	 */
	void enterTextAndOp(XtaDslParser.TextAndOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#textAndOp}.
	 * @param ctx the parse tree
	 */
	void exitTextAndOp(XtaDslParser.TextAndOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#textNotOp}.
	 * @param ctx the parse tree
	 */
	void enterTextNotOp(XtaDslParser.TextNotOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#textNotOp}.
	 * @param ctx the parse tree
	 */
	void exitTextNotOp(XtaDslParser.TextNotOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#assignmentOp}.
	 * @param ctx the parse tree
	 */
	void enterAssignmentOp(XtaDslParser.AssignmentOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#assignmentOp}.
	 * @param ctx the parse tree
	 */
	void exitAssignmentOp(XtaDslParser.AssignmentOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#assignOp}.
	 * @param ctx the parse tree
	 */
	void enterAssignOp(XtaDslParser.AssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#assignOp}.
	 * @param ctx the parse tree
	 */
	void exitAssignOp(XtaDslParser.AssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#addAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterAddAssignOp(XtaDslParser.AddAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#addAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitAddAssignOp(XtaDslParser.AddAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#subAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterSubAssignOp(XtaDslParser.SubAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#subAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitSubAssignOp(XtaDslParser.SubAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#mulAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterMulAssignOp(XtaDslParser.MulAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#mulAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitMulAssignOp(XtaDslParser.MulAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#divAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterDivAssignOp(XtaDslParser.DivAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#divAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitDivAssignOp(XtaDslParser.DivAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#remAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterRemAssignOp(XtaDslParser.RemAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#remAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitRemAssignOp(XtaDslParser.RemAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bwOrAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterBwOrAssignOp(XtaDslParser.BwOrAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bwOrAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitBwOrAssignOp(XtaDslParser.BwOrAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bwAndAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterBwAndAssignOp(XtaDslParser.BwAndAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bwAndAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitBwAndAssignOp(XtaDslParser.BwAndAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bwXorAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterBwXorAssignOp(XtaDslParser.BwXorAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bwXorAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitBwXorAssignOp(XtaDslParser.BwXorAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#shlAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterShlAssignOp(XtaDslParser.ShlAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#shlAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitShlAssignOp(XtaDslParser.ShlAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#shrAssignOp}.
	 * @param ctx the parse tree
	 */
	void enterShrAssignOp(XtaDslParser.ShrAssignOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#shrAssignOp}.
	 * @param ctx the parse tree
	 */
	void exitShrAssignOp(XtaDslParser.ShrAssignOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#logOrOp}.
	 * @param ctx the parse tree
	 */
	void enterLogOrOp(XtaDslParser.LogOrOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#logOrOp}.
	 * @param ctx the parse tree
	 */
	void exitLogOrOp(XtaDslParser.LogOrOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#logAndOp}.
	 * @param ctx the parse tree
	 */
	void enterLogAndOp(XtaDslParser.LogAndOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#logAndOp}.
	 * @param ctx the parse tree
	 */
	void exitLogAndOp(XtaDslParser.LogAndOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bwOrOp}.
	 * @param ctx the parse tree
	 */
	void enterBwOrOp(XtaDslParser.BwOrOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bwOrOp}.
	 * @param ctx the parse tree
	 */
	void exitBwOrOp(XtaDslParser.BwOrOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bwXorOp}.
	 * @param ctx the parse tree
	 */
	void enterBwXorOp(XtaDslParser.BwXorOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bwXorOp}.
	 * @param ctx the parse tree
	 */
	void exitBwXorOp(XtaDslParser.BwXorOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bwAndOp}.
	 * @param ctx the parse tree
	 */
	void enterBwAndOp(XtaDslParser.BwAndOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bwAndOp}.
	 * @param ctx the parse tree
	 */
	void exitBwAndOp(XtaDslParser.BwAndOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#equalityOp}.
	 * @param ctx the parse tree
	 */
	void enterEqualityOp(XtaDslParser.EqualityOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#equalityOp}.
	 * @param ctx the parse tree
	 */
	void exitEqualityOp(XtaDslParser.EqualityOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#eqOp}.
	 * @param ctx the parse tree
	 */
	void enterEqOp(XtaDslParser.EqOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#eqOp}.
	 * @param ctx the parse tree
	 */
	void exitEqOp(XtaDslParser.EqOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#neqOp}.
	 * @param ctx the parse tree
	 */
	void enterNeqOp(XtaDslParser.NeqOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#neqOp}.
	 * @param ctx the parse tree
	 */
	void exitNeqOp(XtaDslParser.NeqOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#relationalOp}.
	 * @param ctx the parse tree
	 */
	void enterRelationalOp(XtaDslParser.RelationalOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#relationalOp}.
	 * @param ctx the parse tree
	 */
	void exitRelationalOp(XtaDslParser.RelationalOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#ltOp}.
	 * @param ctx the parse tree
	 */
	void enterLtOp(XtaDslParser.LtOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#ltOp}.
	 * @param ctx the parse tree
	 */
	void exitLtOp(XtaDslParser.LtOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#leqOp}.
	 * @param ctx the parse tree
	 */
	void enterLeqOp(XtaDslParser.LeqOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#leqOp}.
	 * @param ctx the parse tree
	 */
	void exitLeqOp(XtaDslParser.LeqOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#gtOp}.
	 * @param ctx the parse tree
	 */
	void enterGtOp(XtaDslParser.GtOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#gtOp}.
	 * @param ctx the parse tree
	 */
	void exitGtOp(XtaDslParser.GtOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#geqOp}.
	 * @param ctx the parse tree
	 */
	void enterGeqOp(XtaDslParser.GeqOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#geqOp}.
	 * @param ctx the parse tree
	 */
	void exitGeqOp(XtaDslParser.GeqOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#shiftOp}.
	 * @param ctx the parse tree
	 */
	void enterShiftOp(XtaDslParser.ShiftOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#shiftOp}.
	 * @param ctx the parse tree
	 */
	void exitShiftOp(XtaDslParser.ShiftOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#shlOp}.
	 * @param ctx the parse tree
	 */
	void enterShlOp(XtaDslParser.ShlOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#shlOp}.
	 * @param ctx the parse tree
	 */
	void exitShlOp(XtaDslParser.ShlOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#shrOp}.
	 * @param ctx the parse tree
	 */
	void enterShrOp(XtaDslParser.ShrOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#shrOp}.
	 * @param ctx the parse tree
	 */
	void exitShrOp(XtaDslParser.ShrOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#additiveOp}.
	 * @param ctx the parse tree
	 */
	void enterAdditiveOp(XtaDslParser.AdditiveOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#additiveOp}.
	 * @param ctx the parse tree
	 */
	void exitAdditiveOp(XtaDslParser.AdditiveOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#addOp}.
	 * @param ctx the parse tree
	 */
	void enterAddOp(XtaDslParser.AddOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#addOp}.
	 * @param ctx the parse tree
	 */
	void exitAddOp(XtaDslParser.AddOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#subOp}.
	 * @param ctx the parse tree
	 */
	void enterSubOp(XtaDslParser.SubOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#subOp}.
	 * @param ctx the parse tree
	 */
	void exitSubOp(XtaDslParser.SubOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#multiplicativeOp}.
	 * @param ctx the parse tree
	 */
	void enterMultiplicativeOp(XtaDslParser.MultiplicativeOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#multiplicativeOp}.
	 * @param ctx the parse tree
	 */
	void exitMultiplicativeOp(XtaDslParser.MultiplicativeOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#mulOp}.
	 * @param ctx the parse tree
	 */
	void enterMulOp(XtaDslParser.MulOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#mulOp}.
	 * @param ctx the parse tree
	 */
	void exitMulOp(XtaDslParser.MulOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#divOp}.
	 * @param ctx the parse tree
	 */
	void enterDivOp(XtaDslParser.DivOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#divOp}.
	 * @param ctx the parse tree
	 */
	void exitDivOp(XtaDslParser.DivOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#remOp}.
	 * @param ctx the parse tree
	 */
	void enterRemOp(XtaDslParser.RemOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#remOp}.
	 * @param ctx the parse tree
	 */
	void exitRemOp(XtaDslParser.RemOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#prefixOp}.
	 * @param ctx the parse tree
	 */
	void enterPrefixOp(XtaDslParser.PrefixOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#prefixOp}.
	 * @param ctx the parse tree
	 */
	void exitPrefixOp(XtaDslParser.PrefixOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#preIncOp}.
	 * @param ctx the parse tree
	 */
	void enterPreIncOp(XtaDslParser.PreIncOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#preIncOp}.
	 * @param ctx the parse tree
	 */
	void exitPreIncOp(XtaDslParser.PreIncOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#preDecOp}.
	 * @param ctx the parse tree
	 */
	void enterPreDecOp(XtaDslParser.PreDecOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#preDecOp}.
	 * @param ctx the parse tree
	 */
	void exitPreDecOp(XtaDslParser.PreDecOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#plusOp}.
	 * @param ctx the parse tree
	 */
	void enterPlusOp(XtaDslParser.PlusOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#plusOp}.
	 * @param ctx the parse tree
	 */
	void exitPlusOp(XtaDslParser.PlusOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#minusOp}.
	 * @param ctx the parse tree
	 */
	void enterMinusOp(XtaDslParser.MinusOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#minusOp}.
	 * @param ctx the parse tree
	 */
	void exitMinusOp(XtaDslParser.MinusOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#logNotOp}.
	 * @param ctx the parse tree
	 */
	void enterLogNotOp(XtaDslParser.LogNotOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#logNotOp}.
	 * @param ctx the parse tree
	 */
	void exitLogNotOp(XtaDslParser.LogNotOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#bwNotOp}.
	 * @param ctx the parse tree
	 */
	void enterBwNotOp(XtaDslParser.BwNotOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#bwNotOp}.
	 * @param ctx the parse tree
	 */
	void exitBwNotOp(XtaDslParser.BwNotOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#postfixOp}.
	 * @param ctx the parse tree
	 */
	void enterPostfixOp(XtaDslParser.PostfixOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#postfixOp}.
	 * @param ctx the parse tree
	 */
	void exitPostfixOp(XtaDslParser.PostfixOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#postIncOp}.
	 * @param ctx the parse tree
	 */
	void enterPostIncOp(XtaDslParser.PostIncOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#postIncOp}.
	 * @param ctx the parse tree
	 */
	void exitPostIncOp(XtaDslParser.PostIncOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#postDecOp}.
	 * @param ctx the parse tree
	 */
	void enterPostDecOp(XtaDslParser.PostDecOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#postDecOp}.
	 * @param ctx the parse tree
	 */
	void exitPostDecOp(XtaDslParser.PostDecOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#functionCallOp}.
	 * @param ctx the parse tree
	 */
	void enterFunctionCallOp(XtaDslParser.FunctionCallOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#functionCallOp}.
	 * @param ctx the parse tree
	 */
	void exitFunctionCallOp(XtaDslParser.FunctionCallOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#arrayAccessOp}.
	 * @param ctx the parse tree
	 */
	void enterArrayAccessOp(XtaDslParser.ArrayAccessOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#arrayAccessOp}.
	 * @param ctx the parse tree
	 */
	void exitArrayAccessOp(XtaDslParser.ArrayAccessOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link XtaDslParser#structSelectOp}.
	 * @param ctx the parse tree
	 */
	void enterStructSelectOp(XtaDslParser.StructSelectOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link XtaDslParser#structSelectOp}.
	 * @param ctx the parse tree
	 */
	void exitStructSelectOp(XtaDslParser.StructSelectOpContext ctx);
}