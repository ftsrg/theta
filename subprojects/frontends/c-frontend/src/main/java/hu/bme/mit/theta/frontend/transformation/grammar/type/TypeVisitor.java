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

import static hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleTypeFactory.*;

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser.CastDeclarationSpecifierContext;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser.CastDeclarationSpecifierListContext;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser.TypeSpecifierPointerContext;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.ExpressionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.*;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.Enum;
import java.util.*;
import java.util.stream.Collectors;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;

public class TypeVisitor extends IncludeHandlingCBaseVisitor<CSimpleType> {
    private final DeclarationVisitor declarationVisitor;
    private final TypedefVisitor typedefVisitor;
    private final ParseContext parseContext;
    private final Logger uniqueWarningLogger;

    private static final List<String> standardTypes =
            List.of("int", "char", "long", "short", "void", "float", "double", "unsigned", "_Bool");
    private static final List<String> shorthandTypes =
            List.of("long", "__int128", "short", "unsigned", "_Bool");

    public TypeVisitor(
            DeclarationVisitor declarationVisitor,
            TypedefVisitor typedefVisitor,
            ParseContext parseContext,
            Logger uniqueWarningLogger) {
        this.declarationVisitor = declarationVisitor;
        this.typedefVisitor = typedefVisitor;
        this.parseContext = parseContext;
        this.uniqueWarningLogger = uniqueWarningLogger;
    }

    @Override
    public CSimpleType visitDeclarationSpecifiers(CParser.DeclarationSpecifiersContext ctx) {
        return createCType(ctx.declarationSpecifier());
    }

    @Override
    public CSimpleType visitDeclarationSpecifiers2(CParser.DeclarationSpecifiers2Context ctx) {
        return createCType(ctx.declarationSpecifier());
    }

    @Override
    public CSimpleType visitCastDeclarationSpecifierList(CastDeclarationSpecifierListContext ctx) {
        return createCType(ctx.spec1, ctx.spec2);
    }

    private CSimpleType mergeCTypes(List<CSimpleType> cSimpleTypes) {
        List<CSimpleType> enums =
                cSimpleTypes.stream()
                        .filter(cType -> cType instanceof Enum)
                        .collect(Collectors.toList());
        if (enums.size() > 0) {
            uniqueWarningLogger.write(
                    Level.INFO, "WARNING: enums are not yet supported! Using int instead.\n");
            cSimpleTypes.add(NamedType("int", parseContext, uniqueWarningLogger));
            cSimpleTypes.removeAll(enums);
        }
        List<CSimpleType> namedElements =
                cSimpleTypes.stream()
                        .map(
                                o ->
                                        o instanceof DeclaredName declaredName
                                                ? typedefVisitor
                                                        .getSimpleType(
                                                                declaredName.getDeclaredName())
                                                        .orElse(o)
                                                : o)
                        .filter(o -> o instanceof NamedType)
                        .collect(Collectors.toList());
        if (namedElements.isEmpty()) {
            namedElements.add(NamedType("int", parseContext, uniqueWarningLogger));
        }
        CSimpleType mainType =
                namedElements.get(
                        namedElements.size()
                                - 1); // if typedef, then last element is the associated name
        if (mainType instanceof DeclaredName declaredName) {
            mainType =
                    typedefVisitor.getSimpleType(declaredName.getDeclaredName()).orElse(mainType);
        }

        if (mainType instanceof NamedType namedType
                && shorthandTypes.contains(namedType.getNamedType())) {
            mainType = NamedType("int", parseContext, uniqueWarningLogger);
        } else {
            cSimpleTypes.remove(mainType);
        }

        CSimpleType type = mainType.copyOf().apply(cSimpleTypes);
        // we didn't get explicit signedness
        if (type.isSigned() == null) {
            if (type instanceof NamedType && ((NamedType) type).getNamedType().contains("char")) {
                uniqueWarningLogger.write(
                        Level.INFO,
                        "WARNING: signedness of the type char is implementation specific. Right now"
                                + " it is interpreted as a signed char.\n");
            }
            type.setSigned(true);
        }
        return type;
    }

    @Override
    public CSimpleType visitSpecifierQualifierList(CParser.SpecifierQualifierListContext ctx) {
        return createCType(ctx);
    }

    private CSimpleType createCType(
            CParser.SpecifierQualifierListContext specifierQualifierListContext) {
        List<CSimpleType> cSimpleTypes = new ArrayList<>();
        if (specifierQualifierListContext != null) {
            for (CParser.TypeSpecifierOrQualifierContext typeSpecifierOrQualifierContext :
                    specifierQualifierListContext.typeSpecifierOrQualifier()) {
                CSimpleType qualifierSpecifier = null;
                if (typeSpecifierOrQualifierContext.typeSpecifier() != null) {
                    qualifierSpecifier =
                            typeSpecifierOrQualifierContext.typeSpecifier().accept(this);
                } else if (typeSpecifierOrQualifierContext.typeQualifier() != null) {
                    qualifierSpecifier =
                            typeSpecifierOrQualifierContext.typeQualifier().accept(this);
                }
                if (qualifierSpecifier != null) {
                    cSimpleTypes.add(qualifierSpecifier);
                }
            }
            if (specifierQualifierListContext.typeSpecifierPointer() != null) {
                CSimpleType qualifierSpecifier =
                        specifierQualifierListContext.typeSpecifierPointer().accept(this);
                if (qualifierSpecifier != null) {
                    cSimpleTypes.add(qualifierSpecifier);
                }
            }
        }

        return mergeCTypes(cSimpleTypes);
    }

    private CSimpleType createCType(
            List<CParser.DeclarationSpecifierContext> declarationSpecifierContexts) {
        List<CSimpleType> cSimpleTypes = new ArrayList<>();
        for (CParser.DeclarationSpecifierContext declarationSpecifierContext :
                declarationSpecifierContexts) {
            for (ParseTree child : declarationSpecifierContext.children) {
                CSimpleType ctype = child.accept(this);
                if (ctype != null) {
                    cSimpleTypes.add(ctype);
                }
            }
        }

        return mergeCTypes(cSimpleTypes);
    }

    private CSimpleType createCType(
            List<CastDeclarationSpecifierContext> spec1list, TypeSpecifierPointerContext spec2) {
        List<CSimpleType> cSimpleTypes = new ArrayList<>();
        if (spec2 != null) { // deliberately first!
            CSimpleType ctype = spec2.accept(this);
            if (ctype != null) {
                cSimpleTypes.add(ctype);
            }
        }
        for (CastDeclarationSpecifierContext declarationSpecifierContext : spec1list) {
            for (ParseTree child : declarationSpecifierContext.children) {
                CSimpleType ctype = child.accept(this);
                if (ctype != null) {
                    cSimpleTypes.add(ctype);
                }
            }
        }

        return mergeCTypes(cSimpleTypes);
    }

    @Override
    public CSimpleType visitStorageClassSpecifier(CParser.StorageClassSpecifierContext ctx) {
        switch (ctx.getText()) {
            case "typedef":
                return Typedef();
            case "extern":
                return Extern();
            case "static":
                return null;
            case "auto":
            case "register":
            case "_Thread_local":
                throw new UnsupportedFrontendElementException(
                        "Not yet implemented (" + ctx.getText() + ")");
        }
        throw new UnsupportedFrontendElementException(
                "Storage class specifier not expected: " + ctx.getText());
    }

    @Override
    public CSimpleType visitTypeSpecifierAtomic(CParser.TypeSpecifierAtomicContext ctx) {
        throw new UnsupportedFrontendElementException("Not yet implemented");
    }

    @Override
    public CSimpleType visitTypeSpecifierCompound(CParser.TypeSpecifierCompoundContext ctx) {
        return ctx.structOrUnionSpecifier().accept(this);
    }

    @Override
    public CSimpleType visitTypeSpecifierFunctionPointer(
            CParser.TypeSpecifierFunctionPointerContext ctx) {
        // A function pointer holds a function id, so it is modeled as a pointer-sized value. The
        // pointee is never dereferenced as data, so the return type (plus its own pointer stars)
        // is used as the base type.
        CSimpleType returnType =
                ctx.typeSpecifier() == null
                        ? NamedType("int", parseContext, uniqueWarningLogger)
                        : ctx.typeSpecifier().accept(this);
        if (returnType == null) {
            return null;
        }
        CSimpleType functionPointer = returnType.copyOf();
        functionPointer.incrementPointer(); // the (*) of the function pointer itself
        return functionPointer;
    }

    @Override
    public CSimpleType visitCompoundDefinition(CParser.CompoundDefinitionContext ctx) {
        {
            boolean union = ctx.structOrUnion().Struct() == null;
            String name = null;
            if (ctx.Identifier() != null) {
                name = ctx.Identifier().getText();
            }
            Struct struct =
                    CSimpleTypeFactory.Struct(name, union, parseContext, uniqueWarningLogger);
            for (CParser.StructDeclarationContext structDeclarationContext :
                    ctx.structDeclarationList().structDeclaration()) {
                CParser.SpecifierQualifierListContext specifierQualifierListContext =
                        structDeclarationContext.specifierQualifierList();
                CSimpleType cSimpleType = specifierQualifierListContext.accept(this);
                if (structDeclarationContext.structDeclaratorList() == null) {
                    final var decl = new CDeclaration(cSimpleType);
                    struct.addField(decl);
                } else {
                    for (CParser.StructDeclaratorContext structDeclaratorContext :
                            structDeclarationContext.structDeclaratorList().structDeclarator()) {
                        CDeclaration declaration =
                                structDeclaratorContext.accept(declarationVisitor);
                        if (declaration.getType() == null) {
                            declaration.setType(cSimpleType);
                        }
                        struct.addField(declaration);
                    }
                }
            }
            return struct;
        }
    }

    @Override
    public CSimpleType visitCompoundUsage(CParser.CompoundUsageContext ctx) {
        String text = ctx.Identifier().getText();
        return Struct.getByName(text, ctx.structOrUnion().Struct() == null);
    }

    @Override
    public CSimpleType visitTypeSpecifierEnum(CParser.TypeSpecifierEnumContext ctx) {
        return ctx.enumSpecifier().accept(this);
    }

    @Override
    public CSimpleType visitEnumDefinition(CParser.EnumDefinitionContext ctx) {
        String id = ctx.Identifier() == null ? null : ctx.Identifier().getText();
        Map<String, Optional<Expr<?>>> fields = new LinkedHashMap<>();
        // C enumerators take the previous value + 1 (starting at 0) unless given an explicit
        // constant expression. Register each name -> value so enumerator references resolve later.
        // If an explicit expression cannot be constant-folded (e.g. it uses shifts, which need
        // bitvector arithmetic that is unavailable here), the running value becomes unknown and we
        // stop registering names until the next resolvable explicit value: registering a guessed
        // value would be unsound (a wrong verdict is worse than an unresolved-name error).
        long nextValue = 0;
        boolean valueKnown = true;
        for (CParser.EnumeratorContext enumeratorContext : ctx.enumeratorList().enumerator()) {
            String name = enumeratorContext.enumerationConstant().getText();
            CParser.ConstantExpressionContext expressionContext =
                    enumeratorContext.constantExpression();
            if (expressionContext != null) {
                Long explicit = evaluateEnumConstant(expressionContext);
                valueKnown = explicit != null;
                if (valueKnown) {
                    nextValue = explicit;
                }
            }
            if (valueKnown) {
                Enum.defineConstant(name, nextValue);
                nextValue++;
            }
            fields.put(name, Optional.empty());
        }
        return Enum(id, fields);
    }

    /**
     * Best-effort constant folding of an enumerator's value expression. Returns {@code null} if the
     * expression cannot be evaluated to an integer constant, in which case the caller falls back to
     * the implicit "previous + 1" numbering.
     */
    private Long evaluateEnumConstant(CParser.ConstantExpressionContext ctx) {
        try {
            ExpressionVisitor expressionVisitor =
                    new ExpressionVisitor(
                            Set.of(),
                            parseContext,
                            null,
                            new ArrayDeque<>(List.of(Tuple2.of("", Map.of()))),
                            Map.of(),
                            typedefVisitor,
                            this,
                            uniqueWarningLogger);
            Expr<?> folded = ExprUtils.simplify(ctx.accept(expressionVisitor));
            if (folded instanceof IntLitExpr intLit) {
                return intLit.getValue().longValue();
            }
            if (folded instanceof BvLitExpr bvLit) {
                return BvUtils.neutralBvLitExprToBigInteger(bvLit).longValue();
            }
        } catch (Exception e) {
            // best effort: fall back to implicit numbering
        }
        return null;
    }

    @Override
    public CSimpleType visitEnumUsage(CParser.EnumUsageContext ctx) {
        return NamedType("enum " + ctx.Identifier().getText(), parseContext, uniqueWarningLogger);
    }

    @Override
    public CSimpleType visitTypeSpecifierExtension(CParser.TypeSpecifierExtensionContext ctx) {
        throw new UnsupportedFrontendElementException("Not yet implemented typeSpecifierExtension");
    }

    @Override
    public CSimpleType visitTypeSpecifierPointer(CParser.TypeSpecifierPointerContext ctx) {
        CSimpleType subtype =
                ctx.typeSpecifier() == null
                        ? NamedType("", parseContext, uniqueWarningLogger)
                        : ctx.typeSpecifier().accept(this);
        if (subtype == null) {
            return null;
        }
        for (Token star : ctx.pointer().stars) {
            subtype = subtype.copyOf();
            subtype.incrementPointer();
        }
        return subtype;
    }

    @Override
    public CSimpleType visitTypeSpecifierSimple(CParser.TypeSpecifierSimpleContext ctx) {
        switch (ctx.getText()) {
            case "signed":
                return Signed();
            case "unsigned":
                return Unsigned();
            case "_Bool":
                return NamedType("_Bool", parseContext, uniqueWarningLogger);
            default:
                return NamedType(ctx.getText(), parseContext, uniqueWarningLogger);
        }
    }

    @Override
    public CSimpleType visitTypeSpecifierGccThread(CParser.TypeSpecifierGccThreadContext ctx) {
        return ThreadLocal();
    }

    @Override
    public CSimpleType visitTypeSpecifierFloat(CParser.TypeSpecifierFloatContext ctx) {
        return NamedType("float", parseContext, uniqueWarningLogger);
    }

    @Override
    public CSimpleType visitTypeSpecifierDouble(CParser.TypeSpecifierDoubleContext ctx) {
        return NamedType("double", parseContext, uniqueWarningLogger);
    }

    @Override
    public CSimpleType visitTypeSpecifierTypedefName(CParser.TypeSpecifierTypedefNameContext ctx) {
        Optional<CComplexType> type = typedefVisitor.getType(ctx.getText());
        if (type.isPresent()) {
            CSimpleType origin = type.get().getOrigin().copyOf();
            origin.setTypedef(false);
            return origin;
        } else {
            if (standardTypes.contains(ctx.getText())) {
                return NamedType(ctx.getText(), parseContext, uniqueWarningLogger);
            } else {
                return DeclaredName(ctx.getText());
            }
        }
    }

    @Override
    public CSimpleType visitTypeSpecifierTypeof(CParser.TypeSpecifierTypeofContext ctx) {
        throw new UnsupportedFrontendElementException("Not yet implemented typeSpecifierTypeof");
    }

    @Override
    public CSimpleType visitTypeQualifier(CParser.TypeQualifierContext ctx) {
        switch (ctx.getText()) {
            case "const":
                return null;
            case "restrict":
                throw new UnsupportedFrontendElementException("Not yet implemented 'restrict'!");
            case "volatile":
                return Volatile();
            case "_Atomic":
                return Atomic();
        }
        throw new UnsupportedFrontendElementException(
                "Type qualifier " + ctx.getText() + " not expected!");
    }

    @Override
    public CSimpleType visitFunctionSpecifier(CParser.FunctionSpecifierContext ctx) {
        return null;
    }

    @Override
    public CSimpleType visitAlignmentSpecifier(CParser.AlignmentSpecifierContext ctx) {
        return null;
    }
}
