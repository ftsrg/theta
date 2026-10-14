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
package hu.bme.mit.theta.vmt;

import java.util.List;
import java.util.stream.Collectors;

/** An SMT-LIB s-expression. Atoms keep their source text, so a tree prints back as valid input. */
public sealed interface SExpr permits SExpr.Atom, SExpr.SList {

    record Atom(String text) implements SExpr {
        public boolean isSymbol(String name) {
            return text.equals(name);
        }

        /** The symbol name with SMT-LIB `|...|` quoting removed. */
        public String symbolName() {
            if (text.length() >= 2 && text.startsWith("|") && text.endsWith("|")) {
                return text.substring(1, text.length() - 1);
            }
            return text;
        }

        @Override
        public String toString() {
            return text;
        }
    }

    record SList(List<SExpr> elems) implements SExpr {
        public SList {
            elems = List.copyOf(elems);
        }

        public SExpr get(int i) {
            return elems.get(i);
        }

        public int size() {
            return elems.size();
        }

        /** True if the first element is the symbol {@code head}. */
        public boolean startsWith(String head) {
            return !elems.isEmpty() && elems.get(0) instanceof Atom a && a.isSymbol(head);
        }

        @Override
        public String toString() {
            return elems.stream().map(Object::toString).collect(Collectors.joining(" ", "(", ")"));
        }
    }
}
