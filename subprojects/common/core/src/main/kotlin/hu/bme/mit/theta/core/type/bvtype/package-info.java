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
/**
 * Bitvector type and its expressions. Use {@link hu.bme.mit.theta.core.type.bvtype.BvExprs} to
 * create them. Bitvectors can be used to simulate machine integers that can be signed/unsigned with
 * a fixed range and wraparound overflow semantics. For example, 255+1 on 8 unsigned bits will
 * result in 0.
 *
 * <p>- {@link hu.bme.mit.theta.core.type.bvtype.BvType}: the actual bitvector type
 *
 * <p>- {@link hu.bme.mit.theta.core.type.bvtype.BvLitExpr}: bitvector literal - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvConcatExpr}: bitvector concatenation - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvExtractExpr}: bitvector extraction
 *
 * <p>- {@link hu.bme.mit.theta.core.type.bvtype.BvNegExpr}: unary minus - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvPosExpr}: unary plus - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvAddExpr}: addition - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvSubExpr}: subtraction - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvMulExpr}: multiplication - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvUDivExpr}: unsigned division - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvSDivExpr}: signed division - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvSModExpr}: modulus - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvURemExpr}: unsigned remainder - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvSRemExpr}: signed remainder
 *
 * <p>- {@link hu.bme.mit.theta.core.type.bvtype.BvNotExpr}: bitwise not - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvAndExpr}: bitwise and - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvOrExpr}: bitwise or - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvXorExpr}: bitwise xor - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr}: shift left - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr}: arithmetic shift right - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr}: logical shift right - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr}: rotate left - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr}: rotate right
 *
 * <p>- {@link hu.bme.mit.theta.core.type.bvtype.BvEqExpr}: equal - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvNeqExpr}: not equal - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvUGtExpr}: unsigned greater - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvULtExpr}: unsigned less - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr}: unsigned greater or equal - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvULeqExpr}: unsigned less or equal - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvSGtExpr}: signed greater - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvSLtExpr}: signed less - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr}: signed greater or equal - {@link
 * hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr}: signed less or equal
 */
package hu.bme.mit.theta.core.type.bvtype;
