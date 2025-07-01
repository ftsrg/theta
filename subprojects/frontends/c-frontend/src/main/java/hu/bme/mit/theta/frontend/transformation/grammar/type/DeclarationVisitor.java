/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializerExpr;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CInitializerList;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.util.ArrayList;
import java.util.List;

public class DeclarationVisitor extends CBaseVisitor<CDeclaration> {
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
                    if (context.initializer().initializerList() != null) {
                        checkState(
                                context.initializer().initializerList().designation().size() == 0,
                                "Initializer list designators not yet implemented!");
                        CInitializerList cInitializerList =
                                new CInitializerList(cSimpleType.getActualType(), parseContext);
                        try {
                            for (CParser.InitializerContext initializer :
                                    context.initializer().initializerList().initializers) {
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
                                        null /* TODO: add designator */,
                                        new CExpr(expr, parseContext));
                            }
                            initializerExpression = cInitializerList;
                        } catch (NullPointerException e) {
                            initializerExpression =
                                    new CExpr(
                                            UnsupportedInitializerExpr.getInstance(), parseContext);
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
        return declaration;
    }

    @Override
    public CDeclaration visitStructDeclaratorSimple(CParser.StructDeclaratorSimpleContext ctx) {
        return ctx.declarator().accept(this);
    }

    @Override
    public CDeclaration visitStructDeclaratorConstant(CParser.StructDeclaratorConstantContext ctx) {
        throw new UnsupportedFrontendElementException("Not yet supported!");
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
        if (!(ctx.parameterTypeList() == null || ctx.parameterTypeList().ellipses == null)) {
            uniqueWarningLogger.write(Level.INFO, "WARNING: variable args are not supported!\n");
            decl.setFunc(true);
            return decl;
        }
        if (ctx.parameterTypeList() != null) {
            for (CParser.ParameterDeclarationContext parameterDeclarationContext :
                    ctx.parameterTypeList().parameterList().parameterDeclaration()) {
                decl.addFunctionParam(parameterDeclarationContext.accept(this));
            }
        }
        decl.setFunc(true);
        return decl;
    }

    @Override
    public CDeclaration visitDirectDeclaratorBitField(CParser.DirectDeclaratorBitFieldContext ctx) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }
}
