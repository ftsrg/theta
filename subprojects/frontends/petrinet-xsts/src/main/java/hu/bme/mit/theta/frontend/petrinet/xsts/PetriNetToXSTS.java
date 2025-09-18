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
package hu.bme.mit.theta.frontend.petrinet.xsts;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.CoreDslManager;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.frontend.petrinet.model.*;
import hu.bme.mit.theta.xsts.XSTS;
import java.io.InputStream;
import java.math.BigInteger;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class PetriNetToXSTS {

    private PetriNetToXSTS() {}

    public static XSTS createXSTS(final PetriNet net, final InputStream propStream) {
        return createXSTS(net, propStream, PropType.FULL_EXPLORATION);
    }

    public static XSTS createXSTS(
            final PetriNet net, final InputStream propStream, final PropType propType) {
        final Map<String, VarDecl<IntType>> placeIdToVar = Containers.createMap();

        final List<Expr<BoolType>> initExprs = new ArrayList<>();
        // Create a variable for each place and initialize them
        for (Place place : net.getPlaces()) {
            final VarDecl<IntType> placeVar = Decls.Var(place.getId(), IntType.getInstance());
            placeIdToVar.put(place.getId(), placeVar);
            initExprs.add(
                    Eq(
                            placeVar.getRef(),
                            IntExprs.Int(BigInteger.valueOf(place.getInitialMarking()))));
        }
        final Expr<BoolType> initExpr = And(initExprs);

        final List<Stmt> tranStmts = new ArrayList<>();
        // Create a transition for each variable

        final var transitionToGuard = new HashMap<Transition, Expr<BoolType>>();

        for (Transition transition : net.getTransitions()) {
            final List<Stmt> stmts = new ArrayList<>();
            final Map<VarDecl<IntType>, Long> takesPutsMap = new HashMap<>();

            final var enoughTokensExprs = new ArrayList<Expr<BoolType>>();
            // Check if enough tokens are present and remove input tokens
            for (PTArc inArc : transition.getIncomingArcs()) {
                final Place sourcePlace = inArc.getSource();

                final VarDecl<IntType> placeVar = placeIdToVar.get(sourcePlace.getId());
                final long weight = inArc.getWeight();

                GeqExpr<?> enoughTokensExpr =
                        GeqExpr.create2(placeVar.getRef(), Int(BigInteger.valueOf(weight)));
                enoughTokensExprs.add(enoughTokensExpr);
                final Stmt enoughTokensStmt = AssumeStmt.of(enoughTokensExpr);
                stmts.add(enoughTokensStmt);

                takesPutsMap.merge(placeVar, -weight, Long::sum);
                //				final Stmt removeTokens =
                // AssignStmt.of(placeVar,Sub(placeVar.getRef(),Int(BigInteger.valueOf(weight))));
                //				stmts.add(removeTokens);
            }
            transitionToGuard.put(transition, SmartBoolExprs.And(enoughTokensExprs));

            // Place output tokens
            for (TPArc outArc : transition.getOutgoingArcs()) {
                final Place targetPlace = outArc.getTarget();

                final VarDecl<IntType> placeVar = placeIdToVar.get(targetPlace.getId());
                final long weight = outArc.getWeight();

                takesPutsMap.merge(placeVar, weight, Long::sum);
                //				final Stmt placeTokens =
                // AssignStmt.of(placeVar,Add(placeVar.getRef(),Int(BigInteger.valueOf(weight))));
                //				stmts.add(placeTokens);
            }

            takesPutsMap.forEach(
                    (placeVar, weight) ->
                            stmts.add(
                                    AssignStmt.of(
                                            placeVar,
                                            Add(
                                                    placeVar.getRef(),
                                                    Int(BigInteger.valueOf(weight))))));

            tranStmts.add(SequenceStmt.of(stmts));
        }

        final NonDetStmt tran = NonDetStmt.of(tranStmts);
        final NonDetStmt init = NonDetStmt.of(ImmutableList.of());
        final NonDetStmt env = NonDetStmt.of(ImmutableList.of());
        final Set<VarDecl<?>> ctrlVars = ImmutableSet.of();

        final Expr<BoolType> propExpr;
        if (propType == PropType.DEADLOCK) {
            propExpr = SmartBoolExprs.Or(transitionToGuard.values());
        } else if (propType == PropType.PN_SAFE) {
            propExpr =
                    SmartBoolExprs.And(
                            placeIdToVar.values().stream()
                                    .map((p) -> Leq(p.getRef(), Int(1)))
                                    .toList());
        } else if (propType == PropType.TARGET_MARKING && propStream != null) {
            final Scanner propScanner = new Scanner(propStream).useDelimiter("\\A");
            final String propertyFile = propScanner.hasNext() ? propScanner.next() : "";
            final String property = stripPropFromPropFile(propertyFile).trim();

            final Pattern markingPattern = Pattern.compile("([0-9]+\\s)*[0-9]+");
            final Matcher markingMatcher = markingPattern.matcher(property);

            if (markingMatcher.matches()) {
                final String[] valueStrings = property.split("\\s");
                final Integer[] values =
                        Arrays.stream(valueStrings).map(Integer::parseInt).toArray(Integer[]::new);

                checkArgument(values.length == net.getPlaces().size());
                final List<Expr<BoolType>> exprs = new ArrayList<>();
                for (int i = 0; i < values.length; i++) {
                    exprs.add(
                            Eq(
                                    placeIdToVar.get(net.getPlaces().get(i).getId()).getRef(),
                                    Int(values[i])));
                }
                propExpr = Not(And(exprs));
            } else {
                final CoreDslManager dslManager = new CoreDslManager();
                for (VarDecl<?> decl : placeIdToVar.values()) {
                    dslManager.declare(decl);
                }
                propExpr = cast(dslManager.parseExpr(property), Bool());
            }
        } else if (propType == PropType.FULL_EXPLORATION) {
            propExpr = False();
        } else {
            propExpr = True();
        }

        return new XSTS(ctrlVars, init, tran, env, initExpr, propExpr);
    }

    private static String stripPropFromPropFile(final String propertyFile) {
        int startingCurlyIndex = -1;
        int endingCurlyIndex = propertyFile.length();
        for (int i = 0; i < propertyFile.length(); i++) {
            if (propertyFile.charAt(i) == '{') {
                if (startingCurlyIndex == -1) {
                    startingCurlyIndex = i + 1;
                }
            }
            if (propertyFile.charAt(i) == '}') {
                endingCurlyIndex = i;
            }
        }
        checkArgument(
                startingCurlyIndex > -1 && endingCurlyIndex < propertyFile.length(),
                "Illegally formatted property %s",
                propertyFile);
        return propertyFile.substring(startingCurlyIndex, endingCurlyIndex);
    }
}
