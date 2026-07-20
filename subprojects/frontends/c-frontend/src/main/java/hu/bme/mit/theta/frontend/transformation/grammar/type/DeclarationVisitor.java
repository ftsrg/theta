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
package hu.bme.mit.theta.frontend.transformation.grammar.type;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CInitializerList;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.util.ArrayList;
import java.util.List;

public class DeclarationVisitor extends IncludeHandlingCBaseVisitor<CDeclaration> {
    private final ParseContext parseContext;
    private final FunctionVisitor functionVisitor;
    private final TypedefVisitor typedefVisitor;
    private final TypeVisitor typeVisitor;
    private final Logger uniqueWarningLogger;

    public DeclarationVisitor(
            ParseContext parseContext,
            FunctionVisitor functionVisitor,
            Logger uniqueWarningLogger) {
        this.parseContext = parseContext;
        this.functionVisitor = functionVisitor;
        this.uniqueWarningLogger = uniqueWarningLogger;
        this.typedefVisitor = new TypedefVisitor(this);
        this.typeVisitor = new TypeVisitor(this, typedefVisitor, parseContext, uniqueWarningLogger);
    }

    public TypedefVisitor getTypedefVisitor() {
        return typedefVisitor;
    }

    public TypeVisitor getTypeVisitor() {
        return typeVisitor;
    }

    public List<CDeclaration> getDeclarations(
            CParser.DeclarationSpecifiersContext declSpecContext,
            CParser.InitDeclaratorListContext initDeclContext) {
        return getDeclarations(declSpecContext, initDeclContext, true);
    }

    /**
     * From a single declaration context and initialization list this function produces the
     * corresponding CDeclarations
     *
     * @param declSpecContext declaration context
     * @param initDeclContext initialization list context
     * @return the corresponding CDeclarations
     */
    public List<CDeclaration> getDeclarations(
            CParser.DeclarationSpecifiersContext declSpecContext,
            CParser.InitDeclaratorListContext initDeclContext,
            boolean getInitExpr) {
        List<CDeclaration> ret = new ArrayList<>();
        CSimpleType cSimpleType = declSpecContext.accept(typeVisitor);
        if (cSimpleType.getAssociatedName() != null) {
            CDeclaration cDeclaration = new CDeclaration(cSimpleType.getAssociatedName());
            cDeclaration.setType(cSimpleType);
            cDeclaration.incDerefCounter(cSimpleType.getPointerLevel());
            ret.add(cDeclaration);
        }
        if (initDeclContext != null) {
            for (CParser.InitDeclaratorContext context : initDeclContext.initDeclarator()) {
                CDeclaration declaration = context.declarator().accept(this);
                CStatement initializerExpression;
                if (context.initializer() != null && getInitExpr) {
                    if (context.initializer().bracedPrimaryExpression() != null) {
                        // `= { }` (GNU / C23 empty initializer) has no initializerList at all.
                        final CParser.InitializerListContext initializerList =
                                context.initializer().bracedPrimaryExpression().initializerList();
                        CInitializerList cInitializerList =
                                new CInitializerList(cSimpleType.getActualType(), parseContext);
                        try {
                            // Elements are placed C-style: a designator sets the position, each
                            // element advances it by one. A designation precedes its initializer
                            // among the children, so walk them in order.
                            int nextPosition = 0;
                            for (org.antlr.v4.runtime.tree.ParseTree child :
                                    initializerList == null
                                            ? List.<org.antlr.v4.runtime.tree.ParseTree>of()
                                            : initializerList.children) {
                                if (child instanceof CParser.DesignationContext designation) {
                                    nextPosition =
                                            designatedPosition(designation, cSimpleType);
                                    continue;
                                }
                                if (!(child instanceof CParser.InitializerContext initializer)) {
                                    continue; // comma
                                }
                                Expr<?> expr =
                                        cSimpleType
                                                .getActualType()
                                                .castTo(
                                                        initializer
                                                                .assignmentExpression()
                                                                .accept(functionVisitor)
                                                                .getExpression());
                                parseContext.getMetadata().create(expr, "cType", cSimpleType);
                                cInitializerList.addStatement(
                                        new CExpr(
                                                IntLitExpr.of(
                                                        java.math.BigInteger.valueOf(
                                                                nextPosition++)),
                                                parseContext),
                                        new CExpr(expr, parseContext));
                            }
                            initializerExpression = cInitializerList;
                        } catch (NullPointerException e) {
                            initializerExpression =
                                    new CExpr(new UnsupportedInitializer(), parseContext);
                            parseContext
                                    .getMetadata()
                                    .create(
                                            initializerExpression.getExpression(),
                                            "cType",
                                            cSimpleType);
                        }
                    } else {
                        initializerExpression =
                                context.initializer()
                                        .assignmentExpression()
                                        .accept(functionVisitor);
                    }
                    declaration.setInitExpr(initializerExpression);
                }
                declaration.setType(cSimpleType);
                ret.add(declaration);
            }
        }
        if (cSimpleType.getAssociatedName() == null
                && initDeclContext != null
                && initDeclContext.initDeclarator().size() > 0) {
            ret.get(0).incDerefCounter(cSimpleType.getPointerLevel());
        }
        return ret;
    }

    @Override
    public CDeclaration visitOrdinaryParameterDeclaration(
            CParser.OrdinaryParameterDeclarationContext ctx) {
        CSimpleType cSimpleType = ctx.declarationSpecifiers().accept(typeVisitor);
        CDeclaration declaration = ctx.declarator().accept(this);
        declaration.setType(cSimpleType);
        if (declaration.isFunc()) {
            // C adjusts a parameter of function type to a pointer to function: in
            // `void f(void g(int))`, `g` is a function pointer, not a function.
            declaration.setFunc(false);
            declaration.setFuncPointer(true);
        }
        return declaration;
    }

    /**
     * The element position a designator selects: the field's index for `.name`, the folded
     * constant for `[expr]`. Only single-level designators are supported; member layout is by
     * field index, so both forms land in the same position space.
     */
    private int designatedPosition(
            CParser.DesignationContext designation, CSimpleType cSimpleType) {
        final List<CParser.DesignatorContext> designators =
                designation.designatorList().designator();
        if (designators.size() != 1) {
            throw new UnsupportedFrontendElementException(
                    "Nested initializer designators are not supported: " + designation.getText());
        }
        final CParser.DesignatorContext designator = designators.get(0);
        if (designator.Identifier() != null) {
            if (!(cSimpleType.getActualType()
                    instanceof
                    hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
                                    struct)) {
                throw new UnsupportedFrontendElementException(
                        "Field designator on a non-struct type: " + designation.getText());
            }
            final String fieldName = designator.Identifier().getText();
            final var fields = struct.getFields();
            for (int i = 0; i < fields.size(); i++) {
                if (fields.get(i).get1().equals(fieldName)) {
                    return i;
                }
            }
            throw new UnsupportedFrontendElementException(
                    "Field [%s] not found, available fields are: %s"
                            .formatted(fieldName, struct.getFieldsAsMap().keySet()));
        }
        if (functionVisitor == null) {
            throw new UnsupportedFrontendElementException(
                    "Cannot fold an array designator without a function visitor: "
                            + designation.getText());
        }
        final Expr<?> folded =
                hu.bme.mit.theta.core.utils.ExprUtils.simplify(
                        designator.constantExpression().accept(functionVisitor).getExpression());
        if (folded instanceof IntLitExpr intLit) {
            return intLit.getValue().intValueExact();
        }
        if (folded instanceof hu.bme.mit.theta.core.type.bvtype.BvLitExpr bvLit) {
            return hu.bme.mit.theta.core.utils.BvUtils.neutralBvLitExprToBigInteger(bvLit)
                    .intValueExact();
        }
        throw new UnsupportedFrontendElementException(
                "Array designator is not a constant: " + designation.getText());
    }

    @Override
    public CDeclaration visitStructDeclaratorSimple(CParser.StructDeclaratorSimpleContext ctx) {
        return ctx.declarator().accept(this);
    }

    @Override
    public CDeclaration visitStructDeclaratorConstant(CParser.StructDeclaratorConstantContext ctx) {
        // A bitfield. An unnamed one (`int : 3;`, `int : 0;`) is padding: no field at all.
        // A named one is a field carrying its width, so the struct layout can pack consecutive
        // bitfields into one storage unit and member access can slice that unit.
        if (ctx.declarator() == null) {
            return null;
        }
        final CDeclaration declaration = ctx.declarator().accept(this);
        declaration.setBitfieldWidth(foldBitfieldWidth(ctx.constantExpression()));
        return declaration;
    }

    /** The folded bitfield width, or -1 when it cannot be resolved (falls back to a plain field). */
    private int foldBitfieldWidth(CParser.ConstantExpressionContext ctx) {
        if (functionVisitor == null) {
            return -1;
        }
        try {
            final Expr<?> folded =
                    hu.bme.mit.theta.core.utils.ExprUtils.simplify(
                            ctx.accept(functionVisitor).getExpression());
            if (folded instanceof IntLitExpr intLit) {
                return intLit.getValue().intValueExact();
            }
            if (folded instanceof hu.bme.mit.theta.core.type.bvtype.BvLitExpr bvLit) {
                return hu.bme.mit.theta.core.utils.BvUtils.neutralBvLitExprToBigInteger(bvLit)
                        .intValueExact();
            }
        } catch (RuntimeException e) {
            // fall through
        }
        return -1;
    }

    @Override
    public CDeclaration visitAbstractParameterDeclaration(
            CParser.AbstractParameterDeclarationContext ctx) {
        CSimpleType cSimpleType = ctx.declarationSpecifiers2().accept(typeVisitor);
        checkState(ctx.abstractDeclarator() == null, "Abstract declarators not yet supported!");
        return new CDeclaration(cSimpleType);
    }

    @Override
    public CDeclaration visitDeclarator(CParser.DeclaratorContext ctx) {
        checkState(
                ctx.pointer() == null || ctx.pointer().typeQualifierList().size() == 0,
                "pointers should not have type qualifiers! (not yet implemented)");
        // checkState(ctx.gccDeclaratorExtension().size() == 0, "Cannot do anything with
        // gccDeclaratorExtensions!");
        CDeclaration decl = ctx.directDeclarator().accept(this);

        if (ctx.pointer() != null) {
            int size = ctx.pointer().stars.size();
            decl.incDerefCounter(size);
            // Record where this star binds relative to any array dimensions seen so far, so
            // `T (*p)[N]` (pointer to array) and `T *p[N]` (array of pointers) stay distinct.
            decl.addDeclaratorPointer(size);
        }
        return decl;
    }

    @Override
    public CDeclaration visitDirectDeclaratorId(CParser.DirectDeclaratorIdContext ctx) {
        return new CDeclaration(ctx.getText());
    }

    @Override
    public CDeclaration visitDirectDeclaratorBraces(CParser.DirectDeclaratorBracesContext ctx) {
        return ctx.declarator().accept(this);
    }

    @Override
    public CDeclaration visitDirectDeclaratorArray1(CParser.DirectDeclaratorArray1Context ctx) {
        checkState(
                ctx.typeQualifierList() == null,
                "Type qualifiers inside array declarations are not yet implemented.");

        CDeclaration decl = ctx.directDeclarator().accept(this);
        if (ctx.assignmentExpression() != null) {
            decl.addArrayDimension(ctx.assignmentExpression().accept(functionVisitor));
        } else {
            decl.addArrayDimension(null);
        }
        return decl;
    }

    @Override
    public CDeclaration visitDirectDeclaratorArray2(CParser.DirectDeclaratorArray2Context ctx) {
        throw new UnsupportedFrontendElementException("Not yet implemented!");
    }

    @Override
    public CDeclaration visitDirectDeclaratorArray3(CParser.DirectDeclaratorArray3Context ctx) {
        throw new UnsupportedFrontendElementException("Not yet implemented!");
    }

    @Override
    public CDeclaration visitDirectDeclaratorArray4(CParser.DirectDeclaratorArray4Context ctx) {
        throw new UnsupportedFrontendElementException("Not yet implemented!");
    }

    @Override
    public CDeclaration visitDirectDeclaratorFunctionDecl(
            CParser.DirectDeclaratorFunctionDeclContext ctx) {
        CDeclaration decl = ctx.directDeclarator().accept(this);
        // `int (*fp)(int)` declares a function POINTER variable, while `int foo(int)` (and
        // `int *foo(int)`, a function returning a pointer) declare functions. They are told apart
        // structurally: only the function pointer parenthesizes a pointer declarator, i.e. the
        // direct declarator is `( * fp )`.
        boolean isFunctionPointer =
                ctx.directDeclarator() instanceof CParser.DirectDeclaratorBracesContext braces
                        && braces.declarator().pointer() != null;
        if (!(ctx.parameterTypeList() == null || ctx.parameterTypeList().ellipses == null)) {
            // Only the variadic *tail* is unmodelled (`__builtin_va_arg` yields a nondeterministic
            // value for it). The parameters named before the `...` are ordinary ones, and dropping
            // them left them undeclared inside the function's own body.
            uniqueWarningLogger.write(
                    Level.INFO,
                    "WARNING: variadic arguments are not modeled; reading one yields a"
                            + " nondeterministic value.\n");
        }
        if (ctx.parameterTypeList() != null) {
            for (CParser.ParameterDeclarationContext parameterDeclarationContext :
                    ctx.parameterTypeList().parameterList().parameterDeclaration()) {
                decl.addFunctionParam(parameterDeclarationContext.accept(this));
            }
        }
        decl.setFunc(!isFunctionPointer);
        decl.setFuncPointer(isFunctionPointer);
        return decl;
    }

    @Override
    public CDeclaration visitDirectDeclaratorBitField(CParser.DirectDeclaratorBitFieldContext ctx) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }
}
