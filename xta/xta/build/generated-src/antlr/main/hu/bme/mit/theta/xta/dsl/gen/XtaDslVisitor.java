// Generated from XtaDsl.g4 by ANTLR 4.7.2
package hu.bme.mit.theta.xta.dsl.gen;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link XtaDslParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface XtaDslVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#xta}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitXta(XtaDslParser.XtaContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#iteratorDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIteratorDecl(XtaDslParser.IteratorDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#instantiation}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInstantiation(XtaDslParser.InstantiationContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#system}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSystem(XtaDslParser.SystemContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#parameterList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParameterList(XtaDslParser.ParameterListContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#parameterDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParameterDecl(XtaDslParser.ParameterDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#parameterId}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParameterId(XtaDslParser.ParameterIdContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#functionDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunctionDecl(XtaDslParser.FunctionDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#processDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProcessDecl(XtaDslParser.ProcessDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#processBody}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProcessBody(XtaDslParser.ProcessBodyContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#states}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStates(XtaDslParser.StatesContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#stateDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStateDecl(XtaDslParser.StateDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#commit}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCommit(XtaDslParser.CommitContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#urgent}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUrgent(XtaDslParser.UrgentContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#stateList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStateList(XtaDslParser.StateListContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#init}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInit(XtaDslParser.InitContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#transitions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTransitions(XtaDslParser.TransitionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#transition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTransition(XtaDslParser.TransitionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#transitionOpt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTransitionOpt(XtaDslParser.TransitionOptContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#transitionBody}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTransitionBody(XtaDslParser.TransitionBodyContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#select}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSelect(XtaDslParser.SelectContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#guard}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGuard(XtaDslParser.GuardContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#sync}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSync(XtaDslParser.SyncContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#assign}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssign(XtaDslParser.AssignContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#typeDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeDecl(XtaDslParser.TypeDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#arrayId}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayId(XtaDslParser.ArrayIdContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#arrayIndex}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayIndex(XtaDslParser.ArrayIndexContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#idIndex}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdIndex(XtaDslParser.IdIndexContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#expressionIndex}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpressionIndex(XtaDslParser.ExpressionIndexContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#type}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitType(XtaDslParser.TypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#typePrefix}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypePrefix(XtaDslParser.TypePrefixContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#basicType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBasicType(XtaDslParser.BasicTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#refType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRefType(XtaDslParser.RefTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#voidType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVoidType(XtaDslParser.VoidTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#intType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntType(XtaDslParser.IntTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#clockType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitClockType(XtaDslParser.ClockTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#chanType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitChanType(XtaDslParser.ChanTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#boolType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolType(XtaDslParser.BoolTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#rangeType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRangeType(XtaDslParser.RangeTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#scalarType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitScalarType(XtaDslParser.ScalarTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#structType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStructType(XtaDslParser.StructTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#fieldDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFieldDecl(XtaDslParser.FieldDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#variableDecl}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVariableDecl(XtaDslParser.VariableDeclContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#variableId}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVariableId(XtaDslParser.VariableIdContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#initialiser}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInitialiser(XtaDslParser.InitialiserContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#simpleInitialiser}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSimpleInitialiser(XtaDslParser.SimpleInitialiserContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#compoundInitialiser}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCompoundInitialiser(XtaDslParser.CompoundInitialiserContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#block}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBlock(XtaDslParser.BlockContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#statement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStatement(XtaDslParser.StatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#skipStatement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSkipStatement(XtaDslParser.SkipStatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#expressionStatement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpressionStatement(XtaDslParser.ExpressionStatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#forStatement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitForStatement(XtaDslParser.ForStatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#foreachStatement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitForeachStatement(XtaDslParser.ForeachStatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#whileStatement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitWhileStatement(XtaDslParser.WhileStatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#doStatement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDoStatement(XtaDslParser.DoStatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#ifStatement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIfStatement(XtaDslParser.IfStatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#returnStatement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReturnStatement(XtaDslParser.ReturnStatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#expression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpression(XtaDslParser.ExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#quantifiedExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuantifiedExpression(XtaDslParser.QuantifiedExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#forallExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitForallExpression(XtaDslParser.ForallExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#existsExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExistsExpression(XtaDslParser.ExistsExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#textOrImplyExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTextOrImplyExpression(XtaDslParser.TextOrImplyExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#textAndExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTextAndExpression(XtaDslParser.TextAndExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#textNotExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTextNotExpression(XtaDslParser.TextNotExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#assignmentExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssignmentExpression(XtaDslParser.AssignmentExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#conditionalExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConditionalExpression(XtaDslParser.ConditionalExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#logicalOrExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogicalOrExpression(XtaDslParser.LogicalOrExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#logicalAndExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogicalAndExpression(XtaDslParser.LogicalAndExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bitwiseOrExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseOrExpression(XtaDslParser.BitwiseOrExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bitwiseXorExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseXorExpression(XtaDslParser.BitwiseXorExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bitwiseAndExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBitwiseAndExpression(XtaDslParser.BitwiseAndExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#equalityExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEqualityExpression(XtaDslParser.EqualityExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#relationalExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRelationalExpression(XtaDslParser.RelationalExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#shiftExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitShiftExpression(XtaDslParser.ShiftExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#additiveExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAdditiveExpression(XtaDslParser.AdditiveExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#multiplicativeExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMultiplicativeExpression(XtaDslParser.MultiplicativeExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#prefixExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrefixExpression(XtaDslParser.PrefixExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#postfixExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPostfixExpression(XtaDslParser.PostfixExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#primaryExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrimaryExpression(XtaDslParser.PrimaryExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#trueExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTrueExpression(XtaDslParser.TrueExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#falseExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFalseExpression(XtaDslParser.FalseExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#natExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNatExpression(XtaDslParser.NatExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#idExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdExpression(XtaDslParser.IdExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#parenthesisExpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenthesisExpression(XtaDslParser.ParenthesisExpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#argList}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArgList(XtaDslParser.ArgListContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#textOrImplyOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTextOrImplyOp(XtaDslParser.TextOrImplyOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#textOrOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTextOrOp(XtaDslParser.TextOrOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#textImplyOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTextImplyOp(XtaDslParser.TextImplyOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#textAndOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTextAndOp(XtaDslParser.TextAndOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#textNotOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTextNotOp(XtaDslParser.TextNotOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#assignmentOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssignmentOp(XtaDslParser.AssignmentOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#assignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAssignOp(XtaDslParser.AssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#addAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAddAssignOp(XtaDslParser.AddAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#subAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSubAssignOp(XtaDslParser.SubAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#mulAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMulAssignOp(XtaDslParser.MulAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#divAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDivAssignOp(XtaDslParser.DivAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#remAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRemAssignOp(XtaDslParser.RemAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bwOrAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBwOrAssignOp(XtaDslParser.BwOrAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bwAndAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBwAndAssignOp(XtaDslParser.BwAndAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bwXorAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBwXorAssignOp(XtaDslParser.BwXorAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#shlAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitShlAssignOp(XtaDslParser.ShlAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#shrAssignOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitShrAssignOp(XtaDslParser.ShrAssignOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#logOrOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogOrOp(XtaDslParser.LogOrOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#logAndOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogAndOp(XtaDslParser.LogAndOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bwOrOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBwOrOp(XtaDslParser.BwOrOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bwXorOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBwXorOp(XtaDslParser.BwXorOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bwAndOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBwAndOp(XtaDslParser.BwAndOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#equalityOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEqualityOp(XtaDslParser.EqualityOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#eqOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEqOp(XtaDslParser.EqOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#neqOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNeqOp(XtaDslParser.NeqOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#relationalOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRelationalOp(XtaDslParser.RelationalOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#ltOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLtOp(XtaDslParser.LtOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#leqOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLeqOp(XtaDslParser.LeqOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#gtOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGtOp(XtaDslParser.GtOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#geqOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGeqOp(XtaDslParser.GeqOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#shiftOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitShiftOp(XtaDslParser.ShiftOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#shlOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitShlOp(XtaDslParser.ShlOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#shrOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitShrOp(XtaDslParser.ShrOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#additiveOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAdditiveOp(XtaDslParser.AdditiveOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#addOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAddOp(XtaDslParser.AddOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#subOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSubOp(XtaDslParser.SubOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#multiplicativeOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMultiplicativeOp(XtaDslParser.MultiplicativeOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#mulOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMulOp(XtaDslParser.MulOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#divOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDivOp(XtaDslParser.DivOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#remOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRemOp(XtaDslParser.RemOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#prefixOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPrefixOp(XtaDslParser.PrefixOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#preIncOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPreIncOp(XtaDslParser.PreIncOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#preDecOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPreDecOp(XtaDslParser.PreDecOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#plusOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPlusOp(XtaDslParser.PlusOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#minusOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMinusOp(XtaDslParser.MinusOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#logNotOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogNotOp(XtaDslParser.LogNotOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#bwNotOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBwNotOp(XtaDslParser.BwNotOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#postfixOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPostfixOp(XtaDslParser.PostfixOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#postIncOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPostIncOp(XtaDslParser.PostIncOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#postDecOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPostDecOp(XtaDslParser.PostDecOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#functionCallOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunctionCallOp(XtaDslParser.FunctionCallOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#arrayAccessOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitArrayAccessOp(XtaDslParser.ArrayAccessOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link XtaDslParser#structSelectOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStructSelectOp(XtaDslParser.StructSelectOpContext ctx);
}