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

package hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.ObjObjMap;
import com.koloboke.collect.map.hash.HashObjObjMaps;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.collections.IntStatistics;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.BinaryOperationCache;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.LitExprConverter;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.ArrayList;
import java.util.List;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

public class MddAbstraction {

  private static final BinaryOperationCache<MddVariable, MddNode, RecursiveIntObjMapView<?>> cache =
      new BinaryOperationCache<>();

  public static Expr<BoolType> getExpr(MddNode mddNode, MddVariable variable) {
    final BoundsCollector boundsCollector = new BoundsCollector(mddNode, variable);
    final var exprs = new ArrayList<Expr<BoolType>>();
    for (var entry : boundsCollector.bounds.entrySet()) {
      final MddVariable var = entry.getKey();
      final BoundsCollector.Bounds bounds = entry.getValue();
      final var decl = var.getTraceInfo(Decl.class);
      if (!bounds.hasDefault) {
        if (bounds.lower == bounds.upper) {
          exprs.add(Eq(decl.getRef(), LitExprConverter.toLitExpr(bounds.lower, decl.getType())));
        } else {
          exprs.add(
              And(
                  Geq(decl.getRef(), LitExprConverter.toLitExpr(bounds.lower, decl.getType())),
                  Leq(decl.getRef(), LitExprConverter.toLitExpr(bounds.upper, decl.getType()))
              ));
        }
      }
    }
    return And(exprs);
  }

  public static RecursiveIntObjMapView<?> getAbstraction(MddNode mddNode, MddVariable variable) {

    var cached = cache.getOrNull(variable, mddNode);
    if (cached != null) {
      return cached;
    }

    final BoundsCollector boundsCollector = new BoundsCollector(mddNode, variable);
    final RecursiveIntObjMapView<?> res = representBounds(variable, boundsCollector.bounds);
    cache.addToCache(variable, mddNode, res);

    return res;
  }

  private static RecursiveIntObjMapView<?> representBounds(
      final MddVariable variable,
      final ObjObjMap<MddVariable, BoundsCollector.Bounds> bounds) {
    final RecursiveIntObjMapView<?> continuation;
    if (variable.getLower().isPresent()) {
      continuation = representBounds(variable.getLower().orElseThrow(), bounds);
    } else {
      continuation = RecursiveIntObjMapView.of((IntObjMapView) IntObjMapView.empty());
    }

    final var triple = bounds.get(variable);
    final IntObjMapView<RecursiveIntObjMapView<?>> mapView;
    if (!triple.hasDefault) {
      if (triple.lower == triple.upper) {
        mapView = IntObjMapView.singleton(triple.lower, continuation);
      } else {
        // TODO: canonization of trimmed intobjmapviews could be improved
        mapView =
            new IntObjMapViews.Trimmed<>(
                IntObjMapView.empty(continuation),
                IntSetView.range(triple.lower, triple.upper + 1));
      }
    } else {
      mapView = IntObjMapView.empty(continuation);
    }
    return RecursiveIntObjMapView.of((IntObjMapView) mapView);
  }

  private static class BoundsCollector {

    private final ObjObjMap<MddVariable, BoundsCollector.Bounds> bounds;

    static class Bounds {
      int lower;
      int upper;
      boolean hasDefault;

      Bounds(int lower, int upper, boolean hasDefault) {
        this.lower = lower;
        this.upper = upper;
        this.hasDefault = hasDefault;
      }
    }

    private static BinaryOperationCache<MddNode, MddVariable, ObjObjMap<MddVariable, BoundsCollector.Bounds>>
        cache = new BinaryOperationCache<>();

    public BoundsCollector(MddNode rootNode, MddVariable variable) {
      Preconditions.checkNotNull(rootNode);
      this.bounds = traverse(rootNode, variable);
    }

    private ObjObjMap<MddVariable, BoundsCollector.Bounds> traverse(
        final MddNode node, final MddVariable variable) {
      final var cached = cache.getOrNull(node, variable);
      if (cached != null) {
        return cached;
      }
      if (node.isTerminal()) {
        return HashObjObjMaps.newUpdatableMap();
      }

      Preconditions.checkNotNull(variable);

      for (var c = node.cursor(); c.moveNext(); ) {} // TODO delete later

      final ObjObjMap<MddVariable, BoundsCollector.Bounds> returnValue = HashObjObjMaps.newUpdatableMap();
      final var currentBounds = new BoundsCollector.Bounds(Integer.MAX_VALUE, Integer.MIN_VALUE, false);

      final List<ObjObjMap<MddVariable, BoundsCollector.Bounds>> childBounds = new ArrayList<>();

      final var nodeInterpreter = variable.getNodeInterpreter(node);
      if (nodeInterpreter.defaultValue() != null) {
        final MddNode defaultValue = nodeInterpreter.defaultValue();
        childBounds.add(traverse(defaultValue, variable.getLower().orElse(null)));
        currentBounds.hasDefault = true;
      } else {
        final IntStatistics statistics = nodeInterpreter.statistics();
        currentBounds.lower = statistics.lowestValue();
        currentBounds.upper = statistics.highestValue();

        for (var cur = nodeInterpreter.cursor(); cur.moveNext(); ) {
          if (cur.value() != null) {
            childBounds.add(traverse(cur.value(), variable.getLower().orElse(null)));
          }
        }
      }

      returnValue.put(variable, currentBounds);
      for (final var childBoundMap : childBounds) {
        for (final var entry : childBoundMap.entrySet()) {
          final MddVariable var = entry.getKey();
          final BoundsCollector.Bounds childBoundsForVar = entry.getValue();

          final BoundsCollector.Bounds existingBounds = returnValue.getOrDefault(var, null);
          if (existingBounds == null) {
            returnValue.put(
                var,
                new BoundsCollector.Bounds(
                    childBoundsForVar.lower,
                    childBoundsForVar.upper,
                    childBoundsForVar.hasDefault));
          } else {
            existingBounds.lower =
                Math.min(existingBounds.lower, childBoundsForVar.lower);
            existingBounds.upper =
                Math.max(existingBounds.upper, childBoundsForVar.upper);
            existingBounds.hasDefault |= childBoundsForVar.hasDefault;
          }
        }
      }
      cache.addToCache(node, variable, returnValue);
      return returnValue;
    }
  }

}
