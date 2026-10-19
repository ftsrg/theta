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
/**
 * Bitvector type and its expressions. Use {@link hu.bme.mit.theta.core.type.bvtype.BvExprs} to
 * create them. Bitvectors can be used to simulate machine integers that can be signed/unsigned with
 * a fixed range and wraparound overflow semantics. For example, 255+1 on 8 unsigned bits will
 * result in 0.
 *
 * <p>- {@link hu.bme.mit.theta.core.type.bvtype.BvType}: the actual bitvector type
 *
 * <p>- {@link hu.bme.mit.theta.core.type.BvLitExpr}: bitvector literal - {@link
 * hu.bme.mit.theta.core.type.BvConcatExpr}: bitvector concatenation - {@link
 * hu.bme.mit.theta.core.type.BvExtractExpr}: bitvector extraction
 *
 * <p>- {@link hu.bme.mit.theta.core.type.BvNegExpr}: unary minus - {@link
 * hu.bme.mit.theta.core.type.BvPosExpr}: unary plus - {@link hu.bme.mit.theta.core.type.BvAddExpr}:
 * addition - {@link hu.bme.mit.theta.core.type.BvSubExpr}: subtraction - {@link
 * hu.bme.mit.theta.core.type.BvMulExpr}: multiplication - {@link
 * hu.bme.mit.theta.core.type.BvUDivExpr}: unsigned division - {@link
 * hu.bme.mit.theta.core.type.BvSDivExpr}: signed division - {@link
 * hu.bme.mit.theta.core.type.BvSModExpr}: modulus - {@link hu.bme.mit.theta.core.type.BvURemExpr}:
 * unsigned remainder - {@link hu.bme.mit.theta.core.type.BvSRemExpr}: signed remainder
 *
 * <p>- {@link hu.bme.mit.theta.core.type.BvNotExpr}: bitwise not - {@link
 * hu.bme.mit.theta.core.type.BvAndExpr}: bitwise and - {@link hu.bme.mit.theta.core.type.BvOrExpr}:
 * bitwise or - {@link hu.bme.mit.theta.core.type.BvXorExpr}: bitwise xor - {@link
 * hu.bme.mit.theta.core.type.BvShiftLeftExpr}: shift left - {@link
 * hu.bme.mit.theta.core.type.BvArithShiftRightExpr}: arithmetic shift right - {@link
 * hu.bme.mit.theta.core.type.BvLogicShiftRightExpr}: logical shift right - {@link
 * hu.bme.mit.theta.core.type.BvRotateLeftExpr}: rotate left - {@link
 * hu.bme.mit.theta.core.type.BvRotateRightExpr}: rotate right
 *
 * <p>- {@link hu.bme.mit.theta.core.type.BvEqExpr}: equal - {@link
 * hu.bme.mit.theta.core.type.BvNeqExpr}: not equal - {@link hu.bme.mit.theta.core.type.BvUGtExpr}:
 * unsigned greater - {@link hu.bme.mit.theta.core.type.BvULtExpr}: unsigned less - {@link
 * hu.bme.mit.theta.core.type.BvUGeqExpr}: unsigned greater or equal - {@link
 * hu.bme.mit.theta.core.type.BvULeqExpr}: unsigned less or equal - {@link
 * hu.bme.mit.theta.core.type.BvSGtExpr}: signed greater - {@link
 * hu.bme.mit.theta.core.type.BvSLtExpr}: signed less - {@link
 * hu.bme.mit.theta.core.type.BvSGeqExpr}: signed greater or equal - {@link
 * hu.bme.mit.theta.core.type.BvSLeqExpr}: signed less or equal
 */
package hu.bme.mit.theta.core.type.bvtype;
