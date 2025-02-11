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
package hu.bme.mit.theta.solver;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.ArrayList;
import java.util.List;
import java.util.StringJoiner;
import java.util.stream.Stream;

public record ProofNode(int id, Expr<BoolType> expr, List<ProofNode> children) {
    public AndExpr toExpr() {
        return And(
                Stream.concat(
                                Stream.of(expr),
                                children.stream().flatMap(it -> it.toExpr().getOps().stream()))
                        .toList());
    }

    public int depth() {
        return children.stream().map(ProofNode::depth).max(Integer::compareTo).orElse(0);
    }

    public String toString() {
        final var sj = new StringJoiner(", ");
        children.stream().map(ProofNode::id).forEach(it -> sj.add(it.toString()));
        StringBuilder sb = new StringBuilder();
        sb.append(id).append(": ").append(expr.toString().replaceAll("[\r\n]", " "));

        if (!children.isEmpty()) {
            sb.append(" -> ").append(sj);
        }

        sb.append("\n");
        children.forEach(it -> sb.append(it.toString()));
        return sb.toString();
    }

    public static class Builder {
        final Expr<BoolType> expr;
        final List<ProofNode.Builder> children;

        public Builder(Expr<BoolType> expr) {
            this.expr = expr;
            children = new ArrayList<>();
        }

        public Builder addChild(ProofNode.Builder child) {
            children.add(child);
            return this;
        }

        /** This will fail for non-acyclic proofs, but we don't care, we should never have those. */
        public ProofNode build() {
            return build(0);
        }

        private ProofNode build(int id) {
            final var builtChildren = new ArrayList<ProofNode>();
            for (Builder child : children) {
                final var built = child.build(id);
                builtChildren.add(built);
                id = built.id + 1;
            }
            return new ProofNode(id, expr, builtChildren);
        }
    }
}
