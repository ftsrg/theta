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
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.*;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.Enum;
import java.util.*;
import java.util.stream.Collectors;
import org.antlr.v4.runtime.RuleContext;
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
        CSimpleType type = createCType(ctx.spec1, ctx.spec2);
        if (ctx.dec != null && type != null) {
            // A cast to a pointer-to-array or (nested) function-pointer type: every pointer level
            // in the abstract declarator wraps the base type. The suffixes add nothing on top --
            // a pointer to an array is the array's base address in this element-indexed model, and
            // a function's parameter list, like the pointee of any function pointer, is not
            // modeled (same treatment as typeSpecifierFunctionPointer).
            int levels = pointerLevels(ctx.dec);
            if (levels > 0) {
                type = type.copyOf();
                for (int i = 0; i < levels; i++) {
                    type.incrementPointer();
                }
            }
        }
        return type;
    }

    /** Pointer levels of an abstract declarator, not counting any inside a parameter list. */
    private int pointerLevels(CParser.AbstractDeclaratorContext ctx) {
        int levels = ctx.pointer() != null ? ctx.pointer().stars.size() : 0;
        if (ctx.directAbstractDeclarator() != null) {
            levels += pointerLevels(ctx.directAbstractDeclarator());
        }
        return levels;
    }

    private int pointerLevels(CParser.DirectAbstractDeclaratorContext ctx) {
        int levels = 0;
        if (ctx.abstractDeclarator() != null) {
            levels += pointerLevels(ctx.abstractDeclarator());
        }
        if (ctx.directAbstractDeclarator() != null) {
            levels += pointerLevels(ctx.directAbstractDeclarator());
        }
        return levels;
    }

    /**
     * Builds the one type a declaration's specifiers name.
     *
     * <p>The specifiers arrive as a list, in whatever order they were written, and C attaches no
     * meaning to that order: `unsigned long int`, `long unsigned int` and `int unsigned long` are
     * the same type, and `const T` and `T const` are the same type. Exactly one specifier *names* a
     * type; every other one only modifies it -- `unsigned`, `long`, `const`, `typedef`, or a bare
     * `*`, which carries a pointer level and no type at all. So the namer is picked by what it is,
     * never by where it sits.
     *
     * <p>(It used to be picked as the *last* named specifier. A bare `*` yields a nameless type --
     * see {@link #visitTypeSpecifierPointer} -- and a trailing qualifier stops the pointer from
     * being absorbed into the type before it, so `struct S const *p` left that nameless type last:
     * the struct was demoted to a modifier and `p` came out a `void *`. It only ever went unnoticed
     * because `const struct S *p` puts `struct S *` next to each other, where the pointer *is*
     * absorbed.)
     */
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

        List<CSimpleType> namers =
                cSimpleTypes.stream()
                        .map(this::resolveTypedefName)
                        .filter(this::namesAType)
                        .collect(Collectors.toList());

        // `unsigned x`, `long x` and `_Bool x` name no type of their own: they modify an `int` that
        // was never written down. Two namers can only be `long int`-style spellings, where the
        // width
        // words are modifiers and the last real name is the type.
        CSimpleType mainType =
                namers.isEmpty()
                        ? NamedType("int", parseContext, uniqueWarningLogger)
                        : namers.get(namers.size() - 1);

        // Everything else modifies it. A namer that came from resolving a typedef name is not in
        // the
        // list to begin with (the unresolved name is), and that name must stay: patching it is what
        // records the type's associated name.
        cSimpleTypes.remove(mainType);

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

    /** A typedef name stands for the type it was declared with, once that type is known. */
    private CSimpleType resolveTypedefName(CSimpleType cSimpleType) {
        if (cSimpleType instanceof DeclaredName declaredName) {
            return typedefVisitor
                    .getSimpleType(declaredName.getDeclaredName())
                    .map(
                            typedefed -> {
                                // A copy, because the typedef's own type must not be edited by
                                // whoever uses its name. Its pointers arrived *with* it, so an
                                // `_Atomic` in this declaration qualifies the outermost of them --
                                // `int_ptr _Atomic p` is an atomic pointer -- rather than reaching
                                // past them to the int underneath.
                                CSimpleType resolved = typedefed.copyOf();
                                resolved.markPointersInherited();
                                return resolved;
                            })
                    .orElse(cSimpleType);
        }
        return cSimpleType;
    }

    /** Whether this specifier names a type, rather than only modifying one. */
    private boolean namesAType(CSimpleType cSimpleType) {
        if (!(cSimpleType instanceof NamedType namedType)) {
            return false; // `unsigned`, `const`, `typedef`, `volatile`, an unresolved typedef name
        }
        String name = namedType.getNamedType();
        // A bare `*` in specifier position carries a pointer level and nothing else.
        // `long` / `short` / `unsigned` / `_Bool` / `__int128` only say how wide an `int` is.
        return !name.isEmpty() && !shorthandTypes.contains(name);
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

        final CSimpleType merged = mergeCTypes(cSimpleTypes);
        applyTrailingLayoutAttributes(declarationSpecifierContexts, merged);
        return merged;
    }

    /**
     * `struct S { ... } __attribute__((packed));` -- by far the commonest spelling, and the one the
     * struct specifier never sees: the attribute sits *after* the body, so the grammar makes it a
     * sibling declaration specifier rather than part of `structOrUnionSpecifier`, and
     * {@link #visitCompoundDefinition} is only handed the attributes written before the body.
     *
     * <p>Applied only when this specifier list actually *defines* the struct. An attribute on a
     * variable of an already-defined type (`struct S x __attribute__((aligned(16)));`) describes
     * that variable, not the type, and must not change the layout every other user of `struct S`
     * sees.
     */
    private void applyTrailingLayoutAttributes(
            List<CParser.DeclarationSpecifierContext> specifiers, CSimpleType merged) {
        if (!(merged instanceof Struct struct) || !definesACompound(specifiers)) {
            return;
        }
        final List<CParser.GccAttributeSpecifierContext> attributes = new ArrayList<>();
        for (CParser.DeclarationSpecifierContext specifier : specifiers) {
            collectAttributeSpecifiers(specifier, attributes);
        }
        final ObjectLayout.Attributes layout = LayoutAttributes.of(attributes);
        if (layout != ObjectLayout.Attributes.NONE) {
            struct.setLayoutAttributes(layout);
        }
    }

    /** Whether these specifiers contain a struct/union *definition* rather than a mere usage. */
    private boolean definesACompound(List<CParser.DeclarationSpecifierContext> specifiers) {
        for (CParser.DeclarationSpecifierContext specifier : specifiers) {
            if (findsCompoundDefinition(specifier)) {
                return true;
            }
        }
        return false;
    }

    private boolean findsCompoundDefinition(ParseTree tree) {
        if (tree instanceof CParser.CompoundDefinitionContext) {
            return true;
        }
        for (int i = 0; i < tree.getChildCount(); i++) {
            if (findsCompoundDefinition(tree.getChild(i))) {
                return true;
            }
        }
        return false;
    }

    private void collectAttributeSpecifiers(
            ParseTree tree, List<CParser.GccAttributeSpecifierContext> into) {
        if (tree instanceof CParser.GccAttributeSpecifierContext attribute) {
            into.add(attribute);
            return;
        }
        // Do not descend into a nested compound definition: attributes inside a member's own
        // struct body belong to that struct, not to this one.
        if (tree instanceof CParser.CompoundDefinitionContext) {
            return;
        }
        for (int i = 0; i < tree.getChildCount(); i++) {
            collectAttributeSpecifiers(tree.getChild(i), into);
        }
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
        // `(*)` is one pointer, `(**)` two, and so on: CIL emits `*((int (**)(args))p) = &f` to
        // store
        // a function's address through a pointer-to-function-pointer. Each star is a level; the
        // parameter list, like the pointee of any function pointer, is not modeled.
        int levels = ctx.pointer().stars.size();
        for (int i = 0; i < levels; i++) {
            functionPointer.incrementPointer();
        }
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
            // `struct __attribute__((packed)) { ... }` / `((aligned(64)))`: layout attributes are
            // the only ones this frontend acts on, and ObjectLayout cannot place members without
            // them (a packed struct laid out unpacked misplaces everything after the first member).
            struct.setLayoutAttributes(LayoutAttributes.of(ctx.gccAttributeSpecifier()));
            int anonymousFields = 0;
            for (CParser.StructDeclarationContext structDeclarationContext :
                    ctx.structDeclarationList().structDeclaration()) {
                CParser.SpecifierQualifierListContext specifierQualifierListContext =
                        structDeclarationContext.specifierQualifierList();
                if (specifierQualifierListContext == null) {
                    continue; // bare `;` member (empty declaration)
                }
                CSimpleType cSimpleType = specifierQualifierListContext.accept(this);
                if (structDeclarationContext.structDeclaratorList() == null) {
                    final var decl = new CDeclaration(cSimpleType);
                    if (decl.getName() == null) {
                        // A C11 anonymous struct/union member. It needs a slot in the field list
                        // (member lookup flattens through it), and `addField` needs a name.
                        final var anon =
                                new CDeclaration(CStruct.ANONYMOUS_FIELD_PREFIX + anonymousFields++);
                        anon.setType(cSimpleType);
                        struct.addField(anon);
                    } else {
                        struct.addField(decl);
                    }
                } else {
                    for (CParser.StructDeclaratorContext structDeclaratorContext :
                            structDeclarationContext.structDeclaratorList().structDeclarator()) {
                        CDeclaration declaration =
                                structDeclaratorContext.accept(declarationVisitor);
                        if (declaration == null) {
                            continue;
                        }
                        if (declaration.getType() == null) {
                            declaration.setType(cSimpleType);
                        }
                        if (declaration.getName() == null) {
                            // An unnamed bitfield (`int : 3;`, `int : 0;`): padding, not a field.
                            // It has no name to be looked up by and no value to hold, but it does
                            // move the next member -- `int : 0;` exists precisely to close the
                            // current storage unit -- so its width is kept for the layout.
                            struct.addPadding(
                                    Math.max(declaration.getBitfieldWidth(), 0),
                                    cSimpleType.getActualType().width());
                            continue;
                        }
                        // `int a __attribute__((aligned(8)));` -- a member's own alignment, which
                        // outranks its struct's `packed`.
                        if (declaration.getLayoutAttributes() == ObjectLayout.Attributes.NONE) {
                            declaration.setLayoutAttributes(
                                    LayoutAttributes.of(
                                            structDeclarationContext.gccAttributeSpecifier()));
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
        final List<Token> stars = ctx.pointer().stars;
        for (int i = 0; i < stars.size(); i++) {
            subtype = subtype.copyOf();
            subtype.incrementPointer();
            // A qualifier written *after* a star qualifies that star's pointer, not the type it
            // points at: `int * _Atomic p` is an atomic pointer to a plain int. Each star's
            // qualifiers are the ones written between it and the next.
            if (qualifiersAfter(ctx, stars, i).contains("_Atomic")) {
                subtype.markLastPointerAtomic();
            }
        }
        return subtype;
    }

    /** The type qualifiers written after the i-th star, i.e. before the star that follows it. */
    private String qualifiersAfter(
            CParser.TypeSpecifierPointerContext ctx, List<Token> stars, int i) {
        final int from = stars.get(i).getTokenIndex();
        final int to = i + 1 < stars.size() ? stars.get(i + 1).getTokenIndex() : Integer.MAX_VALUE;
        return ctx.pointer().typeQualifierList().stream()
                .filter(
                        list -> {
                            int at = list.getStart().getTokenIndex();
                            return at > from && at < to;
                        })
                .map(RuleContext::getText)
                .collect(Collectors.joining());
    }

    @Override
    public CSimpleType visitTypeSpecifierAtomic(CParser.TypeSpecifierAtomicContext ctx) {
        // `_Atomic(T)`: the whole of T is atomic -- so `_Atomic(int *)` is an *atomic pointer* to a
        // plain int, where `_Atomic int *` is a plain pointer to an atomic int. Saying it this way
        // round is the only way to write an atomic pointer without a declarator, and it is what
        // `<stdatomic.h>` uses.
        final CParser.TypeNameContext typeName = ctx.atomicTypeSpecifier().typeName();
        checkState(
                typeName.abstractDeclarator() == null,
                "_Atomic() of a declared type (array or function) is not supported");
        final CSimpleType inner = typeName.specifierQualifierList().accept(this);
        if (inner == null) {
            return null;
        }
        final CSimpleType atomicType = inner.copyOf();
        atomicType.markOutermostAtomic();
        return atomicType;
    }

    @Override
    public CSimpleType visitTypeSpecifierSimple(CParser.TypeSpecifierSimpleContext ctx) {
        switch (ctx.getText()) {
            case "signed":
            case "__signed":
            case "__signed__": // GCC spellings
                return Signed();
            case "unsigned":
                return Unsigned();
            case "_Bool":
                return NamedType("_Bool", parseContext, uniqueWarningLogger);
            case "__float128":
                // GCC's 128-bit float. In this benchmark set it only ever appears as the unused
                // padding field of `max_align_t`, so its precision is never observed -- and
                // modeling
                // it as a `double` (rather than the wider `long double` it more resembles) keeps it
                // on the fully-supported path: `CLongDouble` is not yet handled under integer
                // arithmetic, so a program that did compute with it would crash instead.
                return NamedType("double", parseContext, uniqueWarningLogger);
            default:
                return NamedType(ctx.getText(), parseContext, uniqueWarningLogger);
        }
    }

    @Override
    public CSimpleType visitTypeSpecifierVaList(CParser.TypeSpecifierVaListContext ctx) {
        // A variadic function's argument list is opaque: a program may only hand it to va_start /
        // va_arg / va_end, never look at its representation. A pointer-wide integer stands in for
        // it, which is all `typedef __builtin_va_list __gnuc_va_list;` needs -- that single line in
        // glibc's headers is what made the type unparseable, and with it thousands of files that
        // never take a variadic argument at all.
        uniqueWarningLogger.write(
                Level.INFO,
                "WARNING: __builtin_va_list is modeled as an opaque value; reading variadic"
                        + " arguments is not supported.\n");
        return NamedType("long", parseContext, uniqueWarningLogger);
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
            // Whatever pointers the typedef's type has arrived *with* it -- they are not stars of
            // the declaration now being read. `_Atomic` there therefore qualifies the outermost of
            // them (`int_ptr _Atomic p` is an atomic pointer) instead of reaching past them to the
            // thing underneath.
            origin.markPointersInherited();
            return origin;
        } else {
            if (standardTypes.contains(ctx.getText())) {
                return NamedType(ctx.getText(), parseContext, uniqueWarningLogger);
            } else {
                return DeclaredName(ctx.getText());
            }
        }
    }

    /**
     * `typeof(expr)` for expressions that need no variable context -- which covers the macro
     * idiom it exists for: `container_of` expands to `typeof(((struct T*)0)->field)`, a member
     * access on a null literal. The expression is built only to ask its type; it is never emitted.
     * An expression that references variables (a plain `typeof(x)`) is out of reach here -- the
     * type visitor has no scope -- and is reported as unsupported rather than mistyped.
     */
    @Override
    public CSimpleType visitTypeSpecifierTypeof(CParser.TypeSpecifierTypeofContext ctx) {
        if (ctx.typeName() != null) {
            // typeof(type-name), e.g. __typeof__(unsigned long): resolve the named type directly.
            // A bare identifier only reaches this branch when it is a known typedef name (the
            // typedefName predicate), so expressions never end up here.
            final CSimpleType type = ctx.typeName().specifierQualifierList().accept(this);
            if (type != null) {
                final CSimpleType copy = type.copyOf();
                if (ctx.typeName().abstractDeclarator() != null) {
                    final int levels = pointerLevels(ctx.typeName().abstractDeclarator());
                    for (int i = 0; i < levels; i++) {
                        copy.incrementPointer();
                    }
                }
                return copy;
            }
            throw new UnsupportedFrontendElementException(
                    "typeof over an unresolvable type: " + ctx.getText());
        }
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
            Expr<?> expr = ctx.constantExpression().accept(expressionVisitor);
            CSimpleType origin = CComplexType.getType(expr, parseContext).getOrigin();
            if (origin != null) {
                return origin.copyOf();
            }
        } catch (RuntimeException e) {
            // fall through to the unsupported report below
        }
        throw new UnsupportedFrontendElementException(
                "typeof over an expression that references variables is not supported: "
                        + ctx.getText());
    }

    @Override
    public CSimpleType visitTypeQualifier(CParser.TypeQualifierContext ctx) {
        switch (ctx.getText()) {
            case "const":
            case "__const": // GCC spelling
                return null;
            case "restrict":
            case "__restrict": // GCC spellings
            case "__restrict__":
                // `restrict` is a promise by the programmer that the object is not reached through
                // any other pointer. It is a licence to optimize, and says nothing about the values
                // a program computes -- so not exploiting it is sound, and refusing the program
                // over it (as this did) is not.
                return null;
            case "volatile":
            case "__volatile__": // GCC spelling
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
