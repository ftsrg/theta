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
import hu.bme.mit.theta.frontend.transformation.grammar.CLiterals;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CInitializerList;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
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
    /**
     * Gives a declaration the array dimensions its typedef'd specifier carries (`typedef int
     * arr_t[2]; arr_t a;`), which no declarator of its own ever wrote.
     *
     * <p>Appended *after* the declarator's own, because that is the order C reads them in: `typedef
     * int A[2]; A x[3];` makes `x` an `int[3][2]`, so the declarator's `[3]` is the outermost
     * dimension and the typedef's `[2]` the inner one. Getting this backwards still produces an
     * array of the right total size, so only a multi-dimensional case can catch it -- which is what
     * the fixture pins.
     */
    private static void inheritTypedefArrayDimensions(
            CDeclaration declaration, CSimpleType cSimpleType) {
        for (CStatement dimension : cSimpleType.getTypedefArrayDimensions()) {
            declaration.addArrayDimension(dimension);
        }
    }

    public List<CDeclaration> getDeclarations(
            CParser.DeclarationSpecifiersContext declSpecContext,
            CParser.InitDeclaratorListContext initDeclContext,
            boolean getInitExpr) {
        List<CDeclaration> ret = new ArrayList<>();
        CSimpleType cSimpleType = declSpecContext.accept(typeVisitor);
        if (cSimpleType.getAssociatedName() != null) {
            CDeclaration cDeclaration = new CDeclaration(cSimpleType.getAssociatedName());
            cDeclaration.setType(cSimpleType);
            inheritTypedefArrayDimensions(cDeclaration, cSimpleType);
            cDeclaration.incDerefCounter(cSimpleType.getPointerLevel());
            ret.add(cDeclaration);
        }
        if (initDeclContext != null) {
            for (CParser.InitDeclaratorContext context : initDeclContext.initDeclarator()) {
                CDeclaration declaration = context.declarator().accept(this);
                // The initializer's container is the *declared* type, dimensions and all: for
                // `T a[N] = { [i] = {...} }` the array-ness lives on the declarator, not the
                // specifier
                // type, so `getActualType()` (which folds the declarator's array dimensions onto
                // the
                // specifier) is the right container. Passing the bare `cSimpleType.getActualType()`
                // instead read the array's `[i]` designators as struct field indices of the element
                // type -- "Field designator on a non-struct type" once the element was itself an
                // aggregate (the Intel TDX-Module lookup tables). setType now so getActualType sees
                // the specifier.
                declaration.setType(cSimpleType);
                inheritTypedefArrayDimensions(declaration, cSimpleType);
                CStatement initializerExpression;
                if (context.initializer() != null && getInitExpr) {
                    // The name is in scope inside its own initializer (C: the declarator is
                    // complete at the `=`), so bring it into scope before visiting one.
                    if (functionVisitor != null) {
                        functionVisitor.declareBeforeInitializer(declaration);
                    }
                    if (context.initializer().bracedPrimaryExpression() != null) {
                        // `= { }` (GNU / C23 empty initializer) has no initializerList at all.
                        final CParser.InitializerListContext initializerList =
                                context.initializer().bracedPrimaryExpression().initializerList();
                        try {
                            initializerExpression =
                                    buildInitializerList(
                                            initializerList, declaration.getActualType());
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
                        // `char s[8] = "ab"` is an aggregate initializer written without braces,
                        // and it is the only initializer form whose contents the expression path
                        // cannot carry: a string literal folds to the opaque `int(1)`, so the
                        // declaration used to emit `s = 1` -- clobbering the array's own base with
                        // a bare integer, leaving every cell unwritten *and* aliasing `s` onto
                        // whatever object happens to have base id 1. Rewrite it into the brace form
                        // it is equivalent to, so the ordinary aggregate path (including its tail
                        // zero-fill) does the work.
                        final CInitializerList asString =
                                stringInitializerList(
                                        context.initializer().assignmentExpression(),
                                        declaration.getActualType());
                        initializerExpression =
                                asString != null
                                        ? asString
                                        : context.initializer()
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

    /**
     * Builds a (possibly nested) brace initializer into a {@link CInitializerList}.
     *
     * <p>Each element is placed C-style: a designator sets the position, otherwise it takes the
     * next one. A scalar element is folded to its value; a *braced* element (`{{1,2,3},{4,5,6}}`)
     * recurses into a nested list of its own -- which is what lets a multi-dimensional array carry
     * an initializer at all. Before, the loop called {@code initializer.assignmentExpression()}
     * unconditionally, so a nested brace (a `bracedPrimaryExpression`, not an assignment
     * expression) made it NPE and the whole initializer was dropped as unsupported.
     *
     * <p>Leaf scalars are still cast to {@code cSimpleType} and stamped with it, exactly as the
     * flat version did; the c2xcfa side re-casts to the true cell type when it writes the flat
     * object, so the outer type here only has to be consistent, not exact.
     */
    private CInitializerList buildInitializerList(
            CParser.InitializerListContext initializerList, CComplexType containerType) {
        final CInitializerList cInitializerList = new CInitializerList(containerType, parseContext);
        int nextPosition = 0;
        // The remaining designator path when a `.name` reached a field inside an anonymous member,
        // consumed by the value that follows the designation (see buildDesignatedInner); null for a
        // direct field or an array index.
        List<Integer> pendingInnerPath = null;
        for (org.antlr.v4.runtime.tree.ParseTree child :
                initializerList == null
                        ? List.<org.antlr.v4.runtime.tree.ParseTree>of()
                        : initializerList.children) {
            if (child instanceof CParser.DesignationContext designation) {
                final List<Integer> path = designatedPath(designation, containerType);
                nextPosition = path.get(0);
                pendingInnerPath =
                        path.size() > 1 ? new ArrayList<>(path.subList(1, path.size())) : null;
                continue;
            }
            if (!(child instanceof CParser.InitializerContext initializer)) {
                continue; // comma
            }
            // Each element carries its *own* type -- a struct's member at this index, an array's
            // element type -- not the aggregate's. A nested braced initializer (`.lock = { ._v =
            // 0 }`) must therefore recurse with the member's type, or its inner designators resolve
            // against the wrong struct (the `Field [_v] not found, available fields are [lock]`
            // failures on libvsync's `vatomic*` wrappers), and a scalar element is cast to its
            // member type, not to the aggregate.
            final CComplexType elementType = elementTypeAt(containerType, nextPosition);
            final CStatement value =
                    pendingInnerPath == null
                            ? buildLeafValue(elementType, initializer)
                            : buildDesignatedInner(elementType, pendingInnerPath, initializer);
            pendingInnerPath = null;
            cInitializerList.addStatement(
                    new CExpr(
                            IntLitExpr.of(java.math.BigInteger.valueOf(nextPosition++)),
                            parseContext),
                    value);
        }
        return cInitializerList;
    }

    /**
     * One initializer element's value at [type]: a nested list for a braced element (`{ ... }`),
     * otherwise the folded scalar cast to [type].
     */
    private CStatement buildLeafValue(CComplexType type, CParser.InitializerContext initializer) {
        if (initializer.bracedPrimaryExpression() != null) {
            return buildInitializerList(
                    initializer.bracedPrimaryExpression().initializerList(), type);
        }
        final CInitializerList asString =
                stringInitializerList(initializer.assignmentExpression(), type);
        if (asString != null) {
            return asString;
        }
        final Expr<?> expr =
                type.castTo(
                        initializer.assignmentExpression().accept(functionVisitor).getExpression());
        parseContext.getMetadata().create(expr, "cType", type);
        return new CExpr(expr, parseContext);
    }

    /**
     * A designator that named a field inside an anonymous member (`.leaf`, where `leaf` lives in an
     * anonymous {@code union}/{@code struct}) initialises that inner field. The value is wrapped in
     * one nested initializer list per anonymous level, so the flat writer places it in the right
     * cell -- exactly as if the source had written {@code .__theta_anon_0 = { .leaf = value }}.
     */
    private CStatement buildDesignatedInner(
            CComplexType type, List<Integer> innerPath, CParser.InitializerContext initializer) {
        if (innerPath.isEmpty()) {
            return buildLeafValue(type, initializer);
        }
        final int position = innerPath.get(0);
        final CInitializerList nested = new CInitializerList(type, parseContext);
        final CStatement inner =
                buildDesignatedInner(
                        elementTypeAt(type, position),
                        innerPath.subList(1, innerPath.size()),
                        initializer);
        nested.addStatement(
                new CExpr(IntLitExpr.of(java.math.BigInteger.valueOf(position)), parseContext),
                inner);
        return nested;
    }

    /**
     * The brace initializer a string literal is equivalent to, when {@code containerType} is a
     * character array being initialised from one -- {@code null} in every other case, so callers
     * fall through to their ordinary expression handling.
     *
     * <p>The bytes are followed by the terminating NUL, truncated to the declared dimension when
     * that is known: C permits `char a[2] = "ab"`, which stores exactly the two characters and no
     * terminator, and emitting a third cell there would write past the object.
     */
    private CInitializerList stringInitializerList(
            CParser.AssignmentExpressionContext assignment, CComplexType containerType) {
        if (assignment == null || !(containerType instanceof CArray arrayType)) {
            return null;
        }
        if (!(arrayType.getEmbeddedType() instanceof CInteger element) || element.width() != 8) {
            return null;
        }
        final CParser.PrimaryExpressionStringsContext strings = wholeStringLiteral(assignment);
        if (strings == null) {
            return null;
        }
        final List<Integer> bytes = stringLiteralBytes(strings);
        bytes.add(0); // the terminating NUL is part of the literal's value
        final Integer dimension = ObjectLayout.constantDimension(arrayType);
        final int cells = dimension == null ? bytes.size() : Math.min(dimension, bytes.size());
        final CInitializerList list = new CInitializerList(containerType, parseContext);
        for (int index = 0; index < cells; index++) {
            final int value =
                    element.isSsigned() && bytes.get(index) > 127
                            ? bytes.get(index) - 256
                            : bytes.get(index);
            list.addStatement(
                    new CExpr(IntLitExpr.of(java.math.BigInteger.valueOf(index)), parseContext),
                    new CExpr(element.getValue(String.valueOf(value)), parseContext));
        }
        return list;
    }

    /**
     * The string literal an expression consists of *entirely* -- descending only through nodes with
     * a single child, so `"ab"` matches but `f("ab")` or `"ab"[0]` do not.
     */
    private static CParser.PrimaryExpressionStringsContext wholeStringLiteral(
            org.antlr.v4.runtime.tree.ParseTree node) {
        org.antlr.v4.runtime.tree.ParseTree current = node;
        while (!(current instanceof CParser.PrimaryExpressionStringsContext)) {
            if (current.getChildCount() != 1) {
                return null;
            }
            current = current.getChild(0);
        }
        return (CParser.PrimaryExpressionStringsContext) current;
    }

    /**
     * The byte values of a (possibly multi-token, adjacent-concatenated) string literal, escapes
     * decoded. The encoding prefix is dropped: a wide literal is only ever reached here for a
     * one-byte element type, where treating it as bytes is the closest available reading.
     */
    private static List<Integer> stringLiteralBytes(CParser.PrimaryExpressionStringsContext ctx) {
        final List<Integer> bytes = new ArrayList<>();
        for (org.antlr.v4.runtime.tree.TerminalNode token : ctx.StringLiteral()) {
            final String text = token.getText();
            final int open = text.indexOf('"');
            if (open < 0 || text.length() < open + 2) {
                continue;
            }
            bytes.addAll(CLiterals.stringBytes(text.substring(open + 1, text.length() - 1)));
        }
        return bytes;
    }

    /**
     * The type of the element at [position] in an aggregate: a struct's member at that field index
     * (a union's too -- its members share offset 0 but keep distinct indices), an array's element
     * type. Anything else (a scalar being brace-wrapped, or an unknown shape) falls back to the
     * container itself, which is the old whole-aggregate behaviour.
     */
    private CComplexType elementTypeAt(CComplexType containerType, int position) {
        if (containerType
                        instanceof
                        hu.bme.mit.theta.frontend.transformation.model.types.complex.compound
                                        .CStruct
                                struct
                && position >= 0
                && position < struct.getFields().size()) {
            return struct.getFields().get(position).get2();
        }
        if (containerType
                instanceof
                hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
                        array) {
            return array.getEmbeddedType();
        }
        return containerType;
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
     * The path of element positions a designator selects: the field's index for `.name` (descending
     * through anonymous members, so `.leaf` on a struct with an anonymous union member reaches the
     * `leaf` inside it), the folded constant for `[expr]`. Only single-level *source* designators
     * are supported; the returned path has one element for a direct field or array index, more only
     * when an anonymous member had to be flattened through.
     */
    private List<Integer> designatedPath(
            CParser.DesignationContext designation, CComplexType containerType) {
        final List<CParser.DesignatorContext> designators =
                designation.designatorList().designator();
        if (designators.size() != 1) {
            throw new UnsupportedFrontendElementException(
                    "Nested initializer designators are not supported: " + designation.getText());
        }
        final CParser.DesignatorContext designator = designators.get(0);
        if (designator.Identifier() != null) {
            if (!(containerType instanceof CStruct struct)) {
                throw new UnsupportedFrontendElementException(
                        "Field designator on a non-struct type: " + designation.getText());
            }
            final String fieldName = designator.Identifier().getText();
            final List<Integer> path = fieldPath(struct, fieldName);
            if (path == null) {
                throw new UnsupportedFrontendElementException(
                        "Field [%s] not found, available fields are: %s"
                                .formatted(fieldName, struct.getFieldsAsMap().keySet()));
            }
            return path;
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
            return List.of(intLit.getValue().intValueExact());
        }
        if (folded instanceof hu.bme.mit.theta.core.type.bvtype.BvLitExpr bvLit) {
            return List.of(
                    hu.bme.mit.theta.core.utils.BvUtils.neutralBvLitExprToBigInteger(bvLit)
                            .intValueExact());
        }
        throw new UnsupportedFrontendElementException(
                "Array designator is not a constant: " + designation.getText());
    }

    /**
     * The path of field indices reaching [fieldName] in [struct], descending through anonymous
     * struct/union members (the C11 flattening a `.` member access also does), or null if it is not
     * a member at any depth. A direct field gives a one-element path.
     */
    private List<Integer> fieldPath(CStruct struct, String fieldName) {
        final var fields = struct.getFields();
        for (int i = 0; i < fields.size(); i++) {
            if (fields.get(i).get1().equals(fieldName)) {
                final List<Integer> path = new ArrayList<>();
                path.add(i);
                return path;
            }
        }
        for (int i = 0; i < fields.size(); i++) {
            if (fields.get(i).get1().startsWith(CStruct.ANONYMOUS_FIELD_PREFIX)
                    && fields.get(i).get2() instanceof CStruct anonymous) {
                final List<Integer> sub = fieldPath(anonymous, fieldName);
                if (sub != null) {
                    final List<Integer> path = new ArrayList<>();
                    path.add(i);
                    path.addAll(sub);
                    return path;
                }
            }
        }
        return null;
    }

    @Override
    public CDeclaration visitStructDeclaratorSimple(CParser.StructDeclaratorSimpleContext ctx) {
        return ctx.declarator().accept(this);
    }

    @Override
    public CDeclaration visitStructDeclaratorConstant(CParser.StructDeclaratorConstantContext ctx) {
        // A bitfield. An unnamed one (`int : 3;`, `int : 0;`) is padding: it gets no field, but it
        // still moves the next member, so it comes back as a nameless declaration carrying its
        // width for the caller to record as padding (see TypeVisitor#visitCompoundDefinition).
        // A named one is a field carrying its width, so the struct layout can pack consecutive
        // bitfields into one storage unit and member access can slice that unit.
        if (ctx.declarator() == null) {
            final CDeclaration padding = new CDeclaration((String) null);
            padding.setBitfieldWidth(foldBitfieldWidth(ctx.constantExpression()));
            return padding;
        }
        final CDeclaration declaration = ctx.declarator().accept(this);
        declaration.setBitfieldWidth(foldBitfieldWidth(ctx.constantExpression()));
        declaration.setLayoutAttributes(LayoutAttributes.of(ctx.gccAttributeSpecifier()));
        return declaration;
    }

    /** The layout attributes among a declarator's GCC extensions (the rest stay ignored). */
    private ObjectLayout.Attributes declaratorLayoutAttributes(CParser.DeclaratorContext ctx) {
        final List<CParser.GccAttributeSpecifierContext> specifiers = new ArrayList<>();
        for (CParser.GccDeclaratorExtensionContext extension : ctx.gccDeclaratorExtension()) {
            if (extension.gccAttributeSpecifier() != null) {
                specifiers.add(extension.gccAttributeSpecifier());
            }
        }
        if (ctx.gccAttributeSpecifier() != null) {
            specifiers.addAll(ctx.gccAttributeSpecifier());
        }
        return LayoutAttributes.of(specifiers);
    }

    /**
     * The folded bitfield width, or -1 when it cannot be resolved (falls back to a plain field).
     */
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
        // checkState(ctx.gccDeclaratorExtension().size() == 0, "Cannot do anything with
        // gccDeclaratorExtensions!");
        CDeclaration decl = ctx.directDeclarator().accept(this);

        if (ctx.pointer() != null) {
            int size = ctx.pointer().stars.size();
            decl.incDerefCounter(size);
            // Record where this star binds relative to any array dimensions seen so far, so
            // `T (*p)[N]` (pointer to array) and `T *p[N]` (array of pointers) stay distinct.
            decl.addDeclaratorPointer(size);
            // A qualifier after the star inside a declarator -- `void (* _Atomic fp)(void)`, an
            // atomic function pointer. `const`/`volatile`/`restrict` say nothing the model tracks
            // and
            // are ignored; `_Atomic` makes the pointer variable itself atomic (carried to the type
            // in
            // CDeclaration#getActualType). `int * _Atomic p` never reaches here -- there the star
            // is
            // at the type-specifier level (TypeVisitor#visitTypeSpecifierPointer).
            final boolean atomic =
                    ctx.pointer().typeQualifierList().stream()
                            .flatMap(list -> list.typeQualifier().stream())
                            .anyMatch(q -> q.getText().equals("_Atomic"));
            if (atomic) {
                decl.setAtomicPointer(true);
            }
        }
        // `int b __attribute__((aligned(8)));` -- an attribute written after the declarator is a
        // declarator extension, not a declaration specifier, so it arrives here rather than with
        // the type. It raises this member's alignment (and, through it, its struct's).
        final ObjectLayout.Attributes layout = declaratorLayoutAttributes(ctx);
        if (layout != ObjectLayout.Attributes.NONE) {
            decl.setLayoutAttributes(layout);
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
