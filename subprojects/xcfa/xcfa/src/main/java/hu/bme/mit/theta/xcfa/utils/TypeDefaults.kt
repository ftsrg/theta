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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import java.math.BigInteger
import org.kframework.mpfr.BigFloat

/**
 * The zero-like value of a type, for giving a variable a definite starting value.
 *
 * A variable a pass invents has no declaration in the source to initialise it, so anything reading
 * it before its first write reads nothing at all. Analyses differ in how loudly they object -- the
 * OC checker refuses the task outright ("variable ... is not initialized"), others quietly explore a
 * havoc'd value -- so a pass that adds a variable is responsible for also giving it a value.
 */
val Type.defaultValue: LitExpr<out Type>
  get() =
    when (this) {
      is IntType -> Int(0)
      is BoolType -> Bool(false)
      is BvType -> BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, size)
      is RatType -> Rat(0, 1)
      is FpType -> FpUtils.bigFloatToFpLitExpr(BigFloat.zero(significand), this)
      is ArrayType<*, *> ->
        ArrayLitExpr.of(
          listOf(),
          cast(elemType.defaultValue, elemType),
          ArrayType.of(indexType, elemType),
        )
      else -> error("No default value for type $this")
    }
