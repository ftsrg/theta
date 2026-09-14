/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.frontend.transformation.grammar.preprocess;

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Counts the C constructs a program actually uses, for offline study of what predicts which
 * algorithm suits it.
 *
 * It walks the same reachable global declarations {@link BitwiseChecker} does, so what it reports is
 * the program's own code rather than everything its headers happen to declare -- a distinction that
 * matters enormously on preprocessed input, where a trivial program still drags in thousands of
 * lines of libc types.
 *
 * Only construct *kinds* are counted, never an identifier, so the record cannot encode which
 * benchmark it came from.
 */
public class SourceTraitCollector extends IncludeHandlingCBaseVisitor<Void> {

    private final Map<String, Integer> counts = new LinkedHashMap<>();

    private void bump(String key) {
        counts.merge(key, 1, Integer::sum);
    }

    public static Map<String, Integer> collect(
            ParseContext parseContext, List<CParser.ExternalDeclarationContext> contexts) {
        SourceTraitCollector instance = new SourceTraitCollector();
        for (CParser.ExternalDeclarationContext ctx : contexts) {
            try {
                ctx.accept(instance);
            } catch (RuntimeException e) {
                // Never let bookkeeping break a parse: this is diagnostics, not semantics.
                instance.bump("collectorErrors");
            }
        }
        parseContext.setSourceTraits(instance.counts);
        return instance.counts;
    }

    // --- aggregates ---------------------------------------------------------------------------
    @Override
    public Void visitStructOrUnion(CParser.StructOrUnionContext ctx) {
        bump(ctx.getText().startsWith("union") ? "unionKeyword" : "structKeyword");
        return super.visitStructOrUnion(ctx);
    }

    @Override
    public Void visitTypeSpecifierCompound(CParser.TypeSpecifierCompoundContext ctx) {
        bump("compoundType");
        return super.visitTypeSpecifierCompound(ctx);
    }

    @Override
    public Void visitStructDeclaration(CParser.StructDeclarationContext ctx) {
        bump("structField");
        return super.visitStructDeclaration(ctx);
    }

    @Override
    public Void visitDirectDeclaratorBitField(CParser.DirectDeclaratorBitFieldContext ctx) {
        bump("bitField");
        return super.visitDirectDeclaratorBitField(ctx);
    }

    @Override
    public Void visitPostfixExpressionMemberAccess(
            CParser.PostfixExpressionMemberAccessContext ctx) {
        bump("memberAccessDot");
        return super.visitPostfixExpressionMemberAccess(ctx);
    }

    @Override
    public Void visitPostfixExpressionPtrMemberAccess(
            CParser.PostfixExpressionPtrMemberAccessContext ctx) {
        bump("memberAccessArrow");
        return super.visitPostfixExpressionPtrMemberAccess(ctx);
    }

    // --- pointers and arrays ------------------------------------------------------------------
    @Override
    public Void visitPointer(CParser.PointerContext ctx) {
        bump("pointerDeclarator");
        return super.visitPointer(ctx);
    }

    @Override
    public Void visitTypeSpecifierPointer(CParser.TypeSpecifierPointerContext ctx) {
        bump("pointerType");
        return super.visitTypeSpecifierPointer(ctx);
    }

    @Override
    public Void visitTypeSpecifierFunctionPointer(
            CParser.TypeSpecifierFunctionPointerContext ctx) {
        bump("functionPointer");
        return super.visitTypeSpecifierFunctionPointer(ctx);
    }

    @Override
    public Void visitPostfixExpressionBrackets(CParser.PostfixExpressionBracketsContext ctx) {
        bump("arrayIndex");
        return super.visitPostfixExpressionBrackets(ctx);
    }

    // --- control flow -------------------------------------------------------------------------
    @Override
    public Void visitIfStatement(CParser.IfStatementContext ctx) {
        bump("if");
        return super.visitIfStatement(ctx);
    }

    @Override
    public Void visitForStatement(CParser.ForStatementContext ctx) {
        bump("for");
        return super.visitForStatement(ctx);
    }

    @Override
    public Void visitWhileStatement(CParser.WhileStatementContext ctx) {
        bump("while");
        return super.visitWhileStatement(ctx);
    }

    @Override
    public Void visitDoWhileStatement(CParser.DoWhileStatementContext ctx) {
        bump("doWhile");
        return super.visitDoWhileStatement(ctx);
    }

    @Override
    public Void visitSwitchStatement(CParser.SwitchStatementContext ctx) {
        bump("switch");
        return super.visitSwitchStatement(ctx);
    }

    @Override
    public Void visitCaseStatement(CParser.CaseStatementContext ctx) {
        bump("case");
        return super.visitCaseStatement(ctx);
    }

    @Override
    public Void visitGotoStatement(CParser.GotoStatementContext ctx) {
        bump("goto");
        return super.visitGotoStatement(ctx);
    }

    @Override
    public Void visitBreakStatement(CParser.BreakStatementContext ctx) {
        bump("break");
        return super.visitBreakStatement(ctx);
    }

    @Override
    public Void visitContinueStatement(CParser.ContinueStatementContext ctx) {
        bump("continue");
        return super.visitContinueStatement(ctx);
    }

    @Override
    public Void visitReturnStatement(CParser.ReturnStatementContext ctx) {
        bump("return");
        return super.visitReturnStatement(ctx);
    }

    // --- declarations and types ---------------------------------------------------------------
    @Override
    public Void visitFunctionDefinition(CParser.FunctionDefinitionContext ctx) {
        bump("functionDefinition");
        return super.visitFunctionDefinition(ctx);
    }

    @Override
    public Void visitDirectDeclaratorFunctionDecl(
            CParser.DirectDeclaratorFunctionDeclContext ctx) {
        bump("functionDeclarator");
        return super.visitDirectDeclaratorFunctionDecl(ctx);
    }

    @Override
    public Void visitTypeSpecifierEnum(CParser.TypeSpecifierEnumContext ctx) {
        bump("enum");
        return super.visitTypeSpecifierEnum(ctx);
    }

    @Override
    public Void visitTypedefName(CParser.TypedefNameContext ctx) {
        bump("typedefUse");
        return super.visitTypedefName(ctx);
    }

    @Override
    public Void visitTypeSpecifierAtomic(CParser.TypeSpecifierAtomicContext ctx) {
        bump("atomicType");
        return super.visitTypeSpecifierAtomic(ctx);
    }

    @Override
    public Void visitStorageClassSpecifier(CParser.StorageClassSpecifierContext ctx) {
        bump("storage:" + ctx.getText());
        return super.visitStorageClassSpecifier(ctx);
    }

    @Override
    public Void visitTypeQualifier(CParser.TypeQualifierContext ctx) {
        bump("qualifier:" + ctx.getText());
        return super.visitTypeQualifier(ctx);
    }

    @Override
    public Void visitCastExpressionCast(CParser.CastExpressionCastContext ctx) {
        bump("cast");
        return super.visitCastExpressionCast(ctx);
    }

    @Override
    public Void visitInitializerList(CParser.InitializerListContext ctx) {
        bump("initializerList");
        return super.visitInitializerList(ctx);
    }

    @Override
    public Void visitGccAttributeSpecifier(CParser.GccAttributeSpecifierContext ctx) {
        bump("gccAttribute");
        return super.visitGccAttributeSpecifier(ctx);
    }

    @Override
    public Void visitPostfixExpressionIncrement(CParser.PostfixExpressionIncrementContext ctx) {
        bump("increment");
        return super.visitPostfixExpressionIncrement(ctx);
    }

    @Override
    public Void visitPostfixExpressionDecrement(CParser.PostfixExpressionDecrementContext ctx) {
        bump("decrement");
        return super.visitPostfixExpressionDecrement(ctx);
    }

    @Override
    public Void visitConditionalExpression(CParser.ConditionalExpressionContext ctx) {
        if (ctx.getChildCount() > 1) {
            bump("ternary");
        }
        return super.visitConditionalExpression(ctx);
    }

    @Override
    public Void visitArgumentExpressionList(CParser.ArgumentExpressionListContext ctx) {
        bump("callWithArguments");
        return super.visitArgumentExpressionList(ctx);
    }
}
