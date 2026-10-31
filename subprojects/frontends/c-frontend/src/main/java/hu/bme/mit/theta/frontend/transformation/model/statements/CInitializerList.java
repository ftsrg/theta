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
package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

// TODO: designators
public class CInitializerList extends CStatement {
    private final List<Tuple2<Optional<CStatement>, CStatement>> statements;
    private final CComplexType type;
    // Entries whose position the source designated; the others carry the position they follow on.
    private final Set<Integer> designated = new HashSet<>();

    public CInitializerList(CComplexType type, ParseContext parseContext) {
        super(parseContext);
        this.type = type;
        this.statements = new ArrayList<>();
    }

    @Override
    public Expr<?> getExpression() {
        throw new UnsupportedFrontendElementException(
                "Cannot create expression of initializer list.");
    }

    @Override
    public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
        return visitor.visit(this, param);
    }

    public void addStatement(CStatement index, CStatement value) {
        statements.add(Tuple2.of(Optional.ofNullable(index), value));
    }

    /** Adds an entry whose position [index] the source spelled out with a designator. */
    public void addDesignatedStatement(CStatement index, CStatement value) {
        designated.add(statements.size());
        addStatement(index, value);
    }

    /** Whether entry [entry]'s position comes from a designator rather than from its order. */
    public boolean isDesignated(int entry) {
        return designated.contains(entry);
    }

    public List<Tuple2<Optional<CStatement>, CStatement>> getStatements() {
        return statements;
    }

    /**
     * This list in its fully braced form: every aggregate that brace elision (C17 6.7.9p20) fills
     * from the enclosing list gets a list of its own, and every entry carries its position. The
     * local and the global initializers, under every memory model, take this form, so they only
     * follow positions and never track C's running "current object" themselves.
     */
    public CInitializerList braced() {
        return isAggregate(type) ? fill(type, new Entries(this), false) : this;
    }

    /**
     * Fills [type] from [entries]: all of them for its own braces, or, for an elided aggregate,
     * only as many as its members take, stopping at the next designator.
     */
    private CInitializerList fill(CComplexType type, Entries entries, boolean elided) {
        final CInitializerList out = new CInitializerList(type, parseContext);
        final boolean union = type instanceof CStruct struct && struct.isUnion();
        final Integer capacity =
                type instanceof CArray array
                        ? ObjectLayout.constantDimension(array)
                        : Integer.valueOf(((CStruct) type).getFields().size());
        int position = 0;
        int placed = 0;
        while (entries.hasNext()) {
            final Integer designator = entries.designator();
            // An elided aggregate's first entry is designated, if at all, in the enclosing list.
            if (designator != null && elided && placed > 0) {
                break;
            }
            if (designator != null && !(elided && placed == 0)) {
                position = designator;
            }
            // A union takes one member, unless designators name others.
            final boolean full =
                    (capacity != null && position >= capacity)
                            || (union && placed > 0 && (elided || designator == null));
            if (full) {
                if (elided) {
                    break;
                }
                entries.take(); // excess initializer: a constraint violation, ignored
                continue;
            }
            final CComplexType member =
                    type instanceof CArray array
                            ? array.getEmbeddedType()
                            : ((CStruct) type).getFields().get(position).get2();
            final CStatement value = entries.peek();
            final CStatement filled;
            if (value instanceof CInitializerList nested) {
                entries.take();
                filled = isAggregate(member) ? fill(member, new Entries(nested), false) : nested;
            } else if (isAggregate(member) && !isAggregateValue(value)) {
                final int before = entries.position;
                filled = fill(member, entries, true);
                if (entries.position == before) {
                    entries.take(); // nothing to fill (an empty aggregate): drop the entry
                    continue;
                }
            } else {
                entries.take();
                filled = leafValue(member, value);
            }
            out.addDesignatedStatement(
                    new CExpr(IntLitExpr.of(BigInteger.valueOf(position)), parseContext), filled);
            position++;
            placed++;
        }
        return out;
    }

    /** A scalar entry cast to the member it initializes, which elision only now determines. */
    private CStatement leafValue(CComplexType member, CStatement value) {
        if (!(value instanceof CExpr cExpr)
                || cExpr.getExpression() instanceof UnsupportedInitializer
                || member.equals(CComplexType.getType(cExpr.getExpression(), parseContext))) {
            return value;
        }
        final Expr<?> cast = member.castTo(cExpr.getExpression());
        parseContext.getMetadata().create(cast, "cType", member);
        return new CExpr(cast, parseContext);
    }

    private static boolean isAggregate(CComplexType type) {
        return type instanceof CArray || type instanceof CStruct;
    }

    /**
     * Whether [value] is a whole struct or union (a copy), not a scalar to elide braces for. An
     * array-typed value is not: it decays to the pointer a member is initialized with.
     */
    private boolean isAggregateValue(CStatement value) {
        return value instanceof CExpr cExpr
                && !(cExpr.getExpression() instanceof UnsupportedInitializer)
                && CComplexType.getType(cExpr.getExpression(), parseContext) instanceof CStruct;
    }

    /** A cursor over a list's entries, shared with the elided aggregates it fills. */
    private static final class Entries {
        private final CInitializerList list;
        private int position;

        Entries(CInitializerList list) {
            this.list = list;
        }

        /** The position the next entry's designator names, or null when it has none. */
        Integer designator() {
            if (!list.isDesignated(position)) {
                return null;
            }
            final CStatement index = list.statements.get(position).get1().orElseThrow();
            return ((IntLitExpr) index.getExpression()).getValue().intValueExact();
        }

        boolean hasNext() {
            return position < list.statements.size();
        }

        CStatement peek() {
            return list.statements.get(position).get2();
        }

        void take() {
            position++;
        }
    }
}
