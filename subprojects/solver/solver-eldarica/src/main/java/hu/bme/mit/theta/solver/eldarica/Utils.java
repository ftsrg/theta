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
package hu.bme.mit.theta.solver.eldarica;

import static scala.collection.JavaConverters.collectionAsScalaIterableConverter;

import ap.parser.IAtom;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.ITerm;
import ap.terfor.preds.Predicate;
import java.util.List;
import java.util.Optional;
import lazabs.horn.Util;
import lazabs.horn.bottomup.HornClauses;
import lazabs.horn.bottomup.SimpleWrapper;
import scala.Tuple2;
import scala.collection.Iterable;
import scala.collection.JavaConverters;
import scala.collection.immutable.Map;
import scala.collection.immutable.Seq;
import scala.util.Either;

public class Utils {

    static <T> Iterable<T> getIterable(final java.lang.Iterable<T> iterable) {
        return scala.jdk.CollectionConverters.IterableHasAsScala(iterable).asScala();
    }

    static <T> java.lang.Iterable<T> getIterable(final Iterable<T> iterable) {
        return scala.jdk.CollectionConverters.IterableHasAsJava(iterable).asJava();
    }

    static <T> Seq<T> toSeq(List<T> list) {
        return collectionAsScalaIterableConverter(list).asScala().toSeq();
    }

    static <T> Seq<T> toSeq(T t) {
        return collectionAsScalaIterableConverter(List.of(t)).asScala().toSeq();
    }

    public record PredTermFormula(
            Optional<Predicate> predicate, Optional<ITerm> term, Optional<IFormula> formula) {

        public boolean isPredicate() {
            return predicate.isPresent();
        }

        public boolean isTerm() {
            return term.isPresent();
        }

        public boolean isFormula() {
            return formula.isPresent();
        }

        public Predicate asPredicate() {
            return predicate.orElseThrow();
        }

        public ITerm asTerm() {
            return term.orElseThrow();
        }

        public IFormula asFormula() {
            return formula.orElseThrow();
        }

        public IExpression asExpression() {
            if (isTerm()) {
                return asTerm();
            } else if (isFormula()) {
                return asFormula();
            } else {
                throw new ClassCastException("Predicate is not an expression");
            }
        }

        private PredTermFormula(Predicate predicate) {
            this(Optional.of(predicate), Optional.empty(), Optional.empty());
        }

        private PredTermFormula(ITerm term) {
            this(Optional.empty(), Optional.of(term), Optional.empty());
        }

        private PredTermFormula(IFormula formula) {
            this(Optional.empty(), Optional.empty(), Optional.of(formula));
        }

        public static PredTermFormula wrap(Predicate predicate) {
            return new PredTermFormula(predicate);
        }

        public static PredTermFormula wrap(ITerm term) {
            return new PredTermFormula(term);
        }

        public static PredTermFormula wrap(IFormula formula) {
            return new PredTermFormula(formula);
        }
    }

    static Either<Map<Predicate, IFormula>, Util.Dag<Tuple2<IAtom, HornClauses.Clause>>> check(
            java.lang.Iterable<HornClauses.Clause> clauses) {
        return SimpleWrapper.solve(
                getIterable(clauses),
                scala.collection.immutable.Map$.MODULE$.empty(),
                true,
                false,
                false,
                false);
    }

    static <T1, T2> java.util.Map<T1, T2> toMap(scala.collection.Map<T1, T2> map) {
        return JavaConverters.mapAsJavaMapConverter(map).asJava();
    }
}
