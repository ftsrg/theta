/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.pnml;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.CoreDslManager;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.pnml.elements.*;
import hu.bme.mit.theta.xsts.type.XstsType;

import java.io.InputStream;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class PnmlToXSTS {

    private PnmlToXSTS() {
    }

    public static XSTS createXSTS(final PnmlNet net, final InputStream propStream) {
        final Map<String, VarDecl<IntType>> placeIdToVar = Containers.createMap();

        final List<Expr<BoolType>> initExprs = new ArrayList<>();
        // Create a variable for each place and initialize them
        for (PnmlPlace place : net.getPlaces()) {
            final VarDecl<IntType> placeVar = Decls.Var(place.getName(), IntType.getInstance());
            placeIdToVar.put(place.getId(), placeVar);
            initExprs.add(Eq(placeVar.getRef(), Int(place.getInitialMarking())));
        }
        final Expr<BoolType> initExpr = And(initExprs);

        final List<Stmt> tranStmts = new ArrayList<>();
        // Create a transition for each variable
        for (PnmlTransition transition : net.getTransitions()) {
            final List<Stmt> stmts = new ArrayList<>();

            // Check if enough tokens are present and remove input tokens
            for (PnmlArc inArc : transition.getInArcs()) {
                final PnmlNode sourceNode = inArc.getSourceNode();
                checkArgument(sourceNode instanceof PnmlPlace,
                        "Transition %s has an illegal source", transition.getId(), sourceNode.getId());
                final PnmlPlace sourcePlace = (PnmlPlace) sourceNode;

                final VarDecl<IntType> placeVar = placeIdToVar.get(sourcePlace.getId());
                final int weight = inArc.getWeight();

                final Stmt enoughTokens = AssumeStmt.of(
                        GeqExpr.create2(placeVar.getRef(), Int(weight)));
                stmts.add(enoughTokens);

                final Stmt removeTokens = AssignStmt.of(placeVar,
                        Sub(placeVar.getRef(), Int(weight)));
                stmts.add(removeTokens);
            }

            // Place output tokens
            for (PnmlArc outArc : transition.getOutArcs()) {
                final PnmlNode targetNode = outArc.getTargetNode();
                checkArgument(targetNode instanceof PnmlPlace,
                        "Transition %s has an illegal target %s", transition.getId(),
                        targetNode.getId());
                final PnmlPlace targetPlace = (PnmlPlace) targetNode;

                final VarDecl<IntType> placeVar = placeIdToVar.get(targetPlace.getId());
                final int weight = outArc.getWeight();

                final Stmt placeTokens = AssignStmt.of(placeVar,
                        Add(placeVar.getRef(), Int(weight)));
                stmts.add(placeTokens);
            }

            tranStmts.add(SequenceStmt.of(stmts));
        }

        final NonDetStmt tran = NonDetStmt.of(tranStmts);
        final NonDetStmt init = NonDetStmt.of(ImmutableList.of());
        final NonDetStmt env = NonDetStmt.of(ImmutableList.of());

        final Map<VarDecl<?>, XstsType<?>> varToType = ImmutableMap.of();
        final Set<VarDecl<?>> ctrlVars = ImmutableSet.of();

        final Scanner propScanner = new Scanner(propStream).useDelimiter("\\A");
        final String propertyFile = propScanner.hasNext() ? propScanner.next() : "";
        final String property = stripPropFromPropFile(propertyFile).trim();

        final Pattern markingPattern = Pattern.compile("([0-9]+\\s)*[0-9]+");
        final Matcher markingMatcher = markingPattern.matcher(property);

        final Expr<BoolType> propExpr;
        if (markingMatcher.matches()) {
            final String[] valueStrings = property.split("\\s");
            final Integer[] values = Arrays.stream(valueStrings).map(Integer::parseInt)
                    .toArray(Integer[]::new);

            checkArgument(values.length == net.getPlaces().size());
            final List<Expr<BoolType>> exprs = new ArrayList<>();
            for (int i = 0; i < values.length; i++) {
                exprs.add(
                        Eq(placeIdToVar.get(net.getPlaces().get(i).getId()).getRef(), Int(values[i])));
            }
            propExpr = Not(And(exprs));
        } else {
            final CoreDslManager dslManager = new CoreDslManager();
            for (VarDecl<?> decl : placeIdToVar.values()) {
                dslManager.declare(decl);
            }
            propExpr = cast(dslManager.parseExpr(property), Bool());
        }

        return new XSTS(varToType, ctrlVars, init, tran, env, initExpr, propExpr);
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
        checkArgument(startingCurlyIndex > -1 && endingCurlyIndex < propertyFile.length(),
                "Illegally formatted property %s", propertyFile);
        return propertyFile.substring(startingCurlyIndex, endingCurlyIndex);
    }

}
