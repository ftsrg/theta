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
package hu.bme.mit.theta.core.serialization

import hu.bme.mit.theta.core.decl.BasicConstDecl
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.IfStmt
import hu.bme.mit.theta.core.stmt.LoopStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.OrtStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.type.AndExpr
import hu.bme.mit.theta.core.type.ArrayEqExpr
import hu.bme.mit.theta.core.type.ArrayInitExpr
import hu.bme.mit.theta.core.type.ArrayLitExpr
import hu.bme.mit.theta.core.type.ArrayNeqExpr
import hu.bme.mit.theta.core.type.ArrayReadExpr
import hu.bme.mit.theta.core.type.ArrayWriteExpr
import hu.bme.mit.theta.core.type.BvAddExpr
import hu.bme.mit.theta.core.type.BvAndExpr
import hu.bme.mit.theta.core.type.BvArithShiftRightExpr
import hu.bme.mit.theta.core.type.BvConcatExpr
import hu.bme.mit.theta.core.type.BvEqExpr
import hu.bme.mit.theta.core.type.BvExtractExpr
import hu.bme.mit.theta.core.type.BvLitExpr
import hu.bme.mit.theta.core.type.BvLogicShiftRightExpr
import hu.bme.mit.theta.core.type.BvMulExpr
import hu.bme.mit.theta.core.type.BvNegExpr
import hu.bme.mit.theta.core.type.BvNeqExpr
import hu.bme.mit.theta.core.type.BvNotExpr
import hu.bme.mit.theta.core.type.BvOrExpr
import hu.bme.mit.theta.core.type.BvPosExpr
import hu.bme.mit.theta.core.type.BvRotateLeftExpr
import hu.bme.mit.theta.core.type.BvRotateRightExpr
import hu.bme.mit.theta.core.type.BvSDivExpr
import hu.bme.mit.theta.core.type.BvSExtExpr
import hu.bme.mit.theta.core.type.BvSGeqExpr
import hu.bme.mit.theta.core.type.BvSGtExpr
import hu.bme.mit.theta.core.type.BvSLeqExpr
import hu.bme.mit.theta.core.type.BvSLtExpr
import hu.bme.mit.theta.core.type.BvSModExpr
import hu.bme.mit.theta.core.type.BvSRemExpr
import hu.bme.mit.theta.core.type.BvShiftLeftExpr
import hu.bme.mit.theta.core.type.BvSignChangeExpr
import hu.bme.mit.theta.core.type.BvSubExpr
import hu.bme.mit.theta.core.type.BvToIntExpr
import hu.bme.mit.theta.core.type.BvUDivExpr
import hu.bme.mit.theta.core.type.BvUGeqExpr
import hu.bme.mit.theta.core.type.BvUGtExpr
import hu.bme.mit.theta.core.type.BvULeqExpr
import hu.bme.mit.theta.core.type.BvULtExpr
import hu.bme.mit.theta.core.type.BvURemExpr
import hu.bme.mit.theta.core.type.BvXorExpr
import hu.bme.mit.theta.core.type.BvZExtExpr
import hu.bme.mit.theta.core.type.Dereference
import hu.bme.mit.theta.core.type.EnumEqExpr
import hu.bme.mit.theta.core.type.EnumLitExpr
import hu.bme.mit.theta.core.type.EnumNeqExpr
import hu.bme.mit.theta.core.type.ExistsExpr
import hu.bme.mit.theta.core.type.FalseExpr
import hu.bme.mit.theta.core.type.ForallExpr
import hu.bme.mit.theta.core.type.FpAbsExpr
import hu.bme.mit.theta.core.type.FpAddExpr
import hu.bme.mit.theta.core.type.FpAssignExpr
import hu.bme.mit.theta.core.type.FpDivExpr
import hu.bme.mit.theta.core.type.FpEqExpr
import hu.bme.mit.theta.core.type.FpFromBvExpr
import hu.bme.mit.theta.core.type.FpFromIeeeBvExpr
import hu.bme.mit.theta.core.type.FpGeqExpr
import hu.bme.mit.theta.core.type.FpGtExpr
import hu.bme.mit.theta.core.type.FpIsInfiniteExpr
import hu.bme.mit.theta.core.type.FpIsNanExpr
import hu.bme.mit.theta.core.type.FpLeqExpr
import hu.bme.mit.theta.core.type.FpLitExpr
import hu.bme.mit.theta.core.type.FpLtExpr
import hu.bme.mit.theta.core.type.FpMaxExpr
import hu.bme.mit.theta.core.type.FpMinExpr
import hu.bme.mit.theta.core.type.FpMulExpr
import hu.bme.mit.theta.core.type.FpNegExpr
import hu.bme.mit.theta.core.type.FpNeqExpr
import hu.bme.mit.theta.core.type.FpPosExpr
import hu.bme.mit.theta.core.type.FpRemExpr
import hu.bme.mit.theta.core.type.FpRoundToIntegralExpr
import hu.bme.mit.theta.core.type.FpSqrtExpr
import hu.bme.mit.theta.core.type.FpSubExpr
import hu.bme.mit.theta.core.type.FpToBvExpr
import hu.bme.mit.theta.core.type.FpToFpExpr
import hu.bme.mit.theta.core.type.FpToIeeeBvExpr
import hu.bme.mit.theta.core.type.FuncAppExpr
import hu.bme.mit.theta.core.type.FuncLitExpr
import hu.bme.mit.theta.core.type.IffExpr
import hu.bme.mit.theta.core.type.ImplyExpr
import hu.bme.mit.theta.core.type.IntAddExpr
import hu.bme.mit.theta.core.type.IntDivExpr
import hu.bme.mit.theta.core.type.IntEqExpr
import hu.bme.mit.theta.core.type.IntGeqExpr
import hu.bme.mit.theta.core.type.IntGtExpr
import hu.bme.mit.theta.core.type.IntLeqExpr
import hu.bme.mit.theta.core.type.IntLitExpr
import hu.bme.mit.theta.core.type.IntLtExpr
import hu.bme.mit.theta.core.type.IntModExpr
import hu.bme.mit.theta.core.type.IntMulExpr
import hu.bme.mit.theta.core.type.IntNegExpr
import hu.bme.mit.theta.core.type.IntNeqExpr
import hu.bme.mit.theta.core.type.IntPosExpr
import hu.bme.mit.theta.core.type.IntRemExpr
import hu.bme.mit.theta.core.type.IntSubExpr
import hu.bme.mit.theta.core.type.IntToRatExpr
import hu.bme.mit.theta.core.type.InvalidLitExpr
import hu.bme.mit.theta.core.type.IteExpr
import hu.bme.mit.theta.core.type.NotExpr
import hu.bme.mit.theta.core.type.OrExpr
import hu.bme.mit.theta.core.type.PrimeExpr
import hu.bme.mit.theta.core.type.RatAddExpr
import hu.bme.mit.theta.core.type.RatDivExpr
import hu.bme.mit.theta.core.type.RatEqExpr
import hu.bme.mit.theta.core.type.RatGeqExpr
import hu.bme.mit.theta.core.type.RatGtExpr
import hu.bme.mit.theta.core.type.RatLeqExpr
import hu.bme.mit.theta.core.type.RatLitExpr
import hu.bme.mit.theta.core.type.RatLtExpr
import hu.bme.mit.theta.core.type.RatMulExpr
import hu.bme.mit.theta.core.type.RatNegExpr
import hu.bme.mit.theta.core.type.RatNeqExpr
import hu.bme.mit.theta.core.type.RatPosExpr
import hu.bme.mit.theta.core.type.RatSubExpr
import hu.bme.mit.theta.core.type.RatToIntExpr
import hu.bme.mit.theta.core.type.RefExpr
import hu.bme.mit.theta.core.type.Reference
import hu.bme.mit.theta.core.type.TraceableWrapperExpr
import hu.bme.mit.theta.core.type.TrueExpr
import hu.bme.mit.theta.core.type.XorExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatType

/**
 * Every class of core that an [ObjectTable] holds; `ObjectTableTest` checks that none is missing.
 */
object CoreTableClasses : TableClasses() {
  override val names: Set<String> =
    setOf(
      "hu.bme.mit.theta.core.type.ArrayReadExpr",
      "hu.bme.mit.theta.core.type.ArrayWriteExpr",
      "hu.bme.mit.theta.core.type.BvArithShiftRightExpr",
      "hu.bme.mit.theta.core.type.BvLogicShiftRightExpr",
      "hu.bme.mit.theta.core.type.BvRotateLeftExpr",
      "hu.bme.mit.theta.core.type.BvRotateRightExpr",
      "hu.bme.mit.theta.core.type.BvShiftLeftExpr",
      "hu.bme.mit.theta.core.type.BvSDivExpr",
      "hu.bme.mit.theta.core.type.BvUDivExpr",
      "hu.bme.mit.theta.core.type.FpDivExpr",
      "hu.bme.mit.theta.core.type.IntDivExpr",
      "hu.bme.mit.theta.core.type.RatDivExpr",
      "hu.bme.mit.theta.core.type.ArrayEqExpr",
      "hu.bme.mit.theta.core.type.BvEqExpr",
      "hu.bme.mit.theta.core.type.EnumEqExpr",
      "hu.bme.mit.theta.core.type.FpAssignExpr",
      "hu.bme.mit.theta.core.type.FpEqExpr",
      "hu.bme.mit.theta.core.type.IffExpr",
      "hu.bme.mit.theta.core.type.IntEqExpr",
      "hu.bme.mit.theta.core.type.RatEqExpr",
      "hu.bme.mit.theta.core.type.FpMaxExpr",
      "hu.bme.mit.theta.core.type.FpMinExpr",
      "hu.bme.mit.theta.core.type.FpRemExpr",
      "hu.bme.mit.theta.core.type.BvSGeqExpr",
      "hu.bme.mit.theta.core.type.BvUGeqExpr",
      "hu.bme.mit.theta.core.type.FpGeqExpr",
      "hu.bme.mit.theta.core.type.IntGeqExpr",
      "hu.bme.mit.theta.core.type.RatGeqExpr",
      "hu.bme.mit.theta.core.type.BvSGtExpr",
      "hu.bme.mit.theta.core.type.BvUGtExpr",
      "hu.bme.mit.theta.core.type.FpGtExpr",
      "hu.bme.mit.theta.core.type.IntGtExpr",
      "hu.bme.mit.theta.core.type.RatGtExpr",
      "hu.bme.mit.theta.core.type.ImplyExpr",
      "hu.bme.mit.theta.core.type.BvSLeqExpr",
      "hu.bme.mit.theta.core.type.BvULeqExpr",
      "hu.bme.mit.theta.core.type.FpLeqExpr",
      "hu.bme.mit.theta.core.type.IntLeqExpr",
      "hu.bme.mit.theta.core.type.RatLeqExpr",
      "hu.bme.mit.theta.core.type.BvSLtExpr",
      "hu.bme.mit.theta.core.type.BvULtExpr",
      "hu.bme.mit.theta.core.type.FpLtExpr",
      "hu.bme.mit.theta.core.type.IntLtExpr",
      "hu.bme.mit.theta.core.type.RatLtExpr",
      "hu.bme.mit.theta.core.type.BvSModExpr",
      "hu.bme.mit.theta.core.type.IntModExpr",
      "hu.bme.mit.theta.core.type.ArrayNeqExpr",
      "hu.bme.mit.theta.core.type.BvNeqExpr",
      "hu.bme.mit.theta.core.type.EnumNeqExpr",
      "hu.bme.mit.theta.core.type.FpNeqExpr",
      "hu.bme.mit.theta.core.type.IntNeqExpr",
      "hu.bme.mit.theta.core.type.RatNeqExpr",
      "hu.bme.mit.theta.core.type.XorExpr",
      "hu.bme.mit.theta.core.type.BvSRemExpr",
      "hu.bme.mit.theta.core.type.BvURemExpr",
      "hu.bme.mit.theta.core.type.IntRemExpr",
      "hu.bme.mit.theta.core.type.BvSubExpr",
      "hu.bme.mit.theta.core.type.FpSubExpr",
      "hu.bme.mit.theta.core.type.IntSubExpr",
      "hu.bme.mit.theta.core.type.RatSubExpr",
      "hu.bme.mit.theta.core.type.BvConcatExpr",
      "hu.bme.mit.theta.core.type.BvExtractExpr",
      "hu.bme.mit.theta.core.type.BvSExtExpr",
      "hu.bme.mit.theta.core.type.BvZExtExpr",
      "hu.bme.mit.theta.core.type.Dereference",
      "hu.bme.mit.theta.core.type.FuncAppExpr",
      "hu.bme.mit.theta.core.type.IteExpr",
      "hu.bme.mit.theta.core.type.ArrayLitExpr",
      "hu.bme.mit.theta.core.type.FalseExpr",
      "hu.bme.mit.theta.core.type.TrueExpr",
      "hu.bme.mit.theta.core.type.BvLitExpr",
      "hu.bme.mit.theta.core.type.EnumLitExpr",
      "hu.bme.mit.theta.core.type.FpLitExpr",
      "hu.bme.mit.theta.core.type.FuncLitExpr",
      "hu.bme.mit.theta.core.type.IntLitExpr",
      "hu.bme.mit.theta.core.type.InvalidLitExpr",
      "hu.bme.mit.theta.core.type.RatLitExpr",
      "hu.bme.mit.theta.core.type.BvAddExpr",
      "hu.bme.mit.theta.core.type.FpAddExpr",
      "hu.bme.mit.theta.core.type.IntAddExpr",
      "hu.bme.mit.theta.core.type.RatAddExpr",
      "hu.bme.mit.theta.core.type.AndExpr",
      "hu.bme.mit.theta.core.type.ArrayInitExpr",
      "hu.bme.mit.theta.core.type.BvAndExpr",
      "hu.bme.mit.theta.core.type.BvOrExpr",
      "hu.bme.mit.theta.core.type.BvXorExpr",
      "hu.bme.mit.theta.core.type.BvMulExpr",
      "hu.bme.mit.theta.core.type.FpMulExpr",
      "hu.bme.mit.theta.core.type.IntMulExpr",
      "hu.bme.mit.theta.core.type.RatMulExpr",
      "hu.bme.mit.theta.core.type.OrExpr",
      "hu.bme.mit.theta.core.type.RefExpr",
      "hu.bme.mit.theta.core.type.ExistsExpr",
      "hu.bme.mit.theta.core.type.ForallExpr",
      "hu.bme.mit.theta.core.type.Reference",
      "hu.bme.mit.theta.core.type.TraceableWrapperExpr",
      "hu.bme.mit.theta.core.type.BvNotExpr",
      "hu.bme.mit.theta.core.type.BvToIntExpr",
      "hu.bme.mit.theta.core.type.IntToRatExpr",
      "hu.bme.mit.theta.core.type.FpAbsExpr",
      "hu.bme.mit.theta.core.type.FpFromBvExpr",
      "hu.bme.mit.theta.core.type.FpFromIeeeBvExpr",
      "hu.bme.mit.theta.core.type.FpIsInfiniteExpr",
      "hu.bme.mit.theta.core.type.FpIsNanExpr",
      "hu.bme.mit.theta.core.type.FpRoundToIntegralExpr",
      "hu.bme.mit.theta.core.type.FpSqrtExpr",
      "hu.bme.mit.theta.core.type.FpToBvExpr",
      "hu.bme.mit.theta.core.type.FpToFpExpr",
      "hu.bme.mit.theta.core.type.FpToIeeeBvExpr",
      "hu.bme.mit.theta.core.type.BvNegExpr",
      "hu.bme.mit.theta.core.type.FpNegExpr",
      "hu.bme.mit.theta.core.type.IntNegExpr",
      "hu.bme.mit.theta.core.type.RatNegExpr",
      "hu.bme.mit.theta.core.type.NotExpr",
      "hu.bme.mit.theta.core.type.BvPosExpr",
      "hu.bme.mit.theta.core.type.BvSignChangeExpr",
      "hu.bme.mit.theta.core.type.FpPosExpr",
      "hu.bme.mit.theta.core.type.IntPosExpr",
      "hu.bme.mit.theta.core.type.RatPosExpr",
      "hu.bme.mit.theta.core.type.PrimeExpr",
      "hu.bme.mit.theta.core.type.RatToIntExpr",
      "hu.bme.mit.theta.core.stmt.AssignStmt",
      "hu.bme.mit.theta.core.stmt.AssumeStmt",
      "hu.bme.mit.theta.core.stmt.HavocStmt",
      "hu.bme.mit.theta.core.stmt.IfStmt",
      "hu.bme.mit.theta.core.stmt.LoopStmt",
      "hu.bme.mit.theta.core.stmt.MemoryAssignStmt",
      "hu.bme.mit.theta.core.stmt.NonDetStmt",
      "hu.bme.mit.theta.core.stmt.OrtStmt",
      "hu.bme.mit.theta.core.stmt.SequenceStmt",
      "hu.bme.mit.theta.core.stmt.SkipStmt",
      "hu.bme.mit.theta.core.decl.BasicConstDecl",
      "hu.bme.mit.theta.core.decl.IndexedConstDecl",
      "hu.bme.mit.theta.core.decl.ParamDecl",
      "hu.bme.mit.theta.core.decl.VarDecl",
      "hu.bme.mit.theta.core.type.booltype.BoolType",
      "hu.bme.mit.theta.core.type.inttype.IntType",
      "hu.bme.mit.theta.core.type.rattype.RatType",
      "hu.bme.mit.theta.core.type.bvtype.BvType",
      "hu.bme.mit.theta.core.type.fptype.FpType",
      "hu.bme.mit.theta.core.type.arraytype.ArrayType",
      "hu.bme.mit.theta.core.type.functype.FuncType",
      "hu.bme.mit.theta.core.type.enumtype.EnumType",
    )

  override fun entry(name: String): TableClass =
    when (name) {
      "hu.bme.mit.theta.core.type.ArrayReadExpr" ->
        TableClass(
          ArrayReadExpr::class.java,
          ArrayReadExpr.serializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.ArrayWriteExpr" ->
        TableClass(
          ArrayWriteExpr::class.java,
          ArrayWriteExpr.serializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.BvArithShiftRightExpr" ->
        TableClass(BvArithShiftRightExpr::class.java, BvArithShiftRightExpr.serializer())
      "hu.bme.mit.theta.core.type.BvLogicShiftRightExpr" ->
        TableClass(BvLogicShiftRightExpr::class.java, BvLogicShiftRightExpr.serializer())
      "hu.bme.mit.theta.core.type.BvRotateLeftExpr" ->
        TableClass(BvRotateLeftExpr::class.java, BvRotateLeftExpr.serializer())
      "hu.bme.mit.theta.core.type.BvRotateRightExpr" ->
        TableClass(BvRotateRightExpr::class.java, BvRotateRightExpr.serializer())
      "hu.bme.mit.theta.core.type.BvShiftLeftExpr" ->
        TableClass(BvShiftLeftExpr::class.java, BvShiftLeftExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSDivExpr" ->
        TableClass(BvSDivExpr::class.java, BvSDivExpr.serializer())
      "hu.bme.mit.theta.core.type.BvUDivExpr" ->
        TableClass(BvUDivExpr::class.java, BvUDivExpr.serializer())
      "hu.bme.mit.theta.core.type.FpDivExpr" ->
        TableClass(FpDivExpr::class.java, FpDivExpr.serializer())
      "hu.bme.mit.theta.core.type.IntDivExpr" ->
        TableClass(IntDivExpr::class.java, IntDivExpr.serializer())
      "hu.bme.mit.theta.core.type.RatDivExpr" ->
        TableClass(RatDivExpr::class.java, RatDivExpr.serializer())
      "hu.bme.mit.theta.core.type.ArrayEqExpr" ->
        TableClass(
          ArrayEqExpr::class.java,
          ArrayEqExpr.serializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.BvEqExpr" ->
        TableClass(BvEqExpr::class.java, BvEqExpr.serializer())
      "hu.bme.mit.theta.core.type.EnumEqExpr" ->
        TableClass(EnumEqExpr::class.java, EnumEqExpr.serializer())
      "hu.bme.mit.theta.core.type.FpAssignExpr" ->
        TableClass(FpAssignExpr::class.java, FpAssignExpr.serializer())
      "hu.bme.mit.theta.core.type.FpEqExpr" ->
        TableClass(FpEqExpr::class.java, FpEqExpr.serializer())
      "hu.bme.mit.theta.core.type.IffExpr" -> TableClass(IffExpr::class.java, IffExpr.serializer())
      "hu.bme.mit.theta.core.type.IntEqExpr" ->
        TableClass(IntEqExpr::class.java, IntEqExpr.serializer())
      "hu.bme.mit.theta.core.type.RatEqExpr" ->
        TableClass(RatEqExpr::class.java, RatEqExpr.serializer())
      "hu.bme.mit.theta.core.type.FpMaxExpr" ->
        TableClass(FpMaxExpr::class.java, FpMaxExpr.serializer())
      "hu.bme.mit.theta.core.type.FpMinExpr" ->
        TableClass(FpMinExpr::class.java, FpMinExpr.serializer())
      "hu.bme.mit.theta.core.type.FpRemExpr" ->
        TableClass(FpRemExpr::class.java, FpRemExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSGeqExpr" ->
        TableClass(BvSGeqExpr::class.java, BvSGeqExpr.serializer())
      "hu.bme.mit.theta.core.type.BvUGeqExpr" ->
        TableClass(BvUGeqExpr::class.java, BvUGeqExpr.serializer())
      "hu.bme.mit.theta.core.type.FpGeqExpr" ->
        TableClass(FpGeqExpr::class.java, FpGeqExpr.serializer())
      "hu.bme.mit.theta.core.type.IntGeqExpr" ->
        TableClass(IntGeqExpr::class.java, IntGeqExpr.serializer())
      "hu.bme.mit.theta.core.type.RatGeqExpr" ->
        TableClass(RatGeqExpr::class.java, RatGeqExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSGtExpr" ->
        TableClass(BvSGtExpr::class.java, BvSGtExpr.serializer())
      "hu.bme.mit.theta.core.type.BvUGtExpr" ->
        TableClass(BvUGtExpr::class.java, BvUGtExpr.serializer())
      "hu.bme.mit.theta.core.type.FpGtExpr" ->
        TableClass(FpGtExpr::class.java, FpGtExpr.serializer())
      "hu.bme.mit.theta.core.type.IntGtExpr" ->
        TableClass(IntGtExpr::class.java, IntGtExpr.serializer())
      "hu.bme.mit.theta.core.type.RatGtExpr" ->
        TableClass(RatGtExpr::class.java, RatGtExpr.serializer())
      "hu.bme.mit.theta.core.type.ImplyExpr" ->
        TableClass(ImplyExpr::class.java, ImplyExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSLeqExpr" ->
        TableClass(BvSLeqExpr::class.java, BvSLeqExpr.serializer())
      "hu.bme.mit.theta.core.type.BvULeqExpr" ->
        TableClass(BvULeqExpr::class.java, BvULeqExpr.serializer())
      "hu.bme.mit.theta.core.type.FpLeqExpr" ->
        TableClass(FpLeqExpr::class.java, FpLeqExpr.serializer())
      "hu.bme.mit.theta.core.type.IntLeqExpr" ->
        TableClass(IntLeqExpr::class.java, IntLeqExpr.serializer())
      "hu.bme.mit.theta.core.type.RatLeqExpr" ->
        TableClass(RatLeqExpr::class.java, RatLeqExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSLtExpr" ->
        TableClass(BvSLtExpr::class.java, BvSLtExpr.serializer())
      "hu.bme.mit.theta.core.type.BvULtExpr" ->
        TableClass(BvULtExpr::class.java, BvULtExpr.serializer())
      "hu.bme.mit.theta.core.type.FpLtExpr" ->
        TableClass(FpLtExpr::class.java, FpLtExpr.serializer())
      "hu.bme.mit.theta.core.type.IntLtExpr" ->
        TableClass(IntLtExpr::class.java, IntLtExpr.serializer())
      "hu.bme.mit.theta.core.type.RatLtExpr" ->
        TableClass(RatLtExpr::class.java, RatLtExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSModExpr" ->
        TableClass(BvSModExpr::class.java, BvSModExpr.serializer())
      "hu.bme.mit.theta.core.type.IntModExpr" ->
        TableClass(IntModExpr::class.java, IntModExpr.serializer())
      "hu.bme.mit.theta.core.type.ArrayNeqExpr" ->
        TableClass(
          ArrayNeqExpr::class.java,
          ArrayNeqExpr.serializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.BvNeqExpr" ->
        TableClass(BvNeqExpr::class.java, BvNeqExpr.serializer())
      "hu.bme.mit.theta.core.type.EnumNeqExpr" ->
        TableClass(EnumNeqExpr::class.java, EnumNeqExpr.serializer())
      "hu.bme.mit.theta.core.type.FpNeqExpr" ->
        TableClass(FpNeqExpr::class.java, FpNeqExpr.serializer())
      "hu.bme.mit.theta.core.type.IntNeqExpr" ->
        TableClass(IntNeqExpr::class.java, IntNeqExpr.serializer())
      "hu.bme.mit.theta.core.type.RatNeqExpr" ->
        TableClass(RatNeqExpr::class.java, RatNeqExpr.serializer())
      "hu.bme.mit.theta.core.type.XorExpr" -> TableClass(XorExpr::class.java, XorExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSRemExpr" ->
        TableClass(BvSRemExpr::class.java, BvSRemExpr.serializer())
      "hu.bme.mit.theta.core.type.BvURemExpr" ->
        TableClass(BvURemExpr::class.java, BvURemExpr.serializer())
      "hu.bme.mit.theta.core.type.IntRemExpr" ->
        TableClass(IntRemExpr::class.java, IntRemExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSubExpr" ->
        TableClass(BvSubExpr::class.java, BvSubExpr.serializer())
      "hu.bme.mit.theta.core.type.FpSubExpr" ->
        TableClass(FpSubExpr::class.java, FpSubExpr.serializer())
      "hu.bme.mit.theta.core.type.IntSubExpr" ->
        TableClass(IntSubExpr::class.java, IntSubExpr.serializer())
      "hu.bme.mit.theta.core.type.RatSubExpr" ->
        TableClass(RatSubExpr::class.java, RatSubExpr.serializer())
      "hu.bme.mit.theta.core.type.BvConcatExpr" ->
        TableClass(BvConcatExpr::class.java, BvConcatExpr.serializer())
      "hu.bme.mit.theta.core.type.BvExtractExpr" ->
        TableClass(BvExtractExpr::class.java, BvExtractExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSExtExpr" ->
        TableClass(BvSExtExpr::class.java, BvSExtExpr.serializer())
      "hu.bme.mit.theta.core.type.BvZExtExpr" ->
        TableClass(BvZExtExpr::class.java, BvZExtExpr.serializer())
      "hu.bme.mit.theta.core.type.Dereference" ->
        TableClass(
          Dereference::class.java,
          Dereference.serializer(
            TypeReferenceSerializer,
            TypeReferenceSerializer,
            TypeReferenceSerializer,
          ),
        )
      "hu.bme.mit.theta.core.type.FuncAppExpr" ->
        TableClass(
          FuncAppExpr::class.java,
          FuncAppExpr.serializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.IteExpr" ->
        TableClass(IteExpr::class.java, IteExpr.serializer(TypeReferenceSerializer))
      "hu.bme.mit.theta.core.type.ArrayLitExpr" ->
        TableClass(
          ArrayLitExpr::class.java,
          ArrayLitExpr.serializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.FalseExpr" ->
        TableClass(FalseExpr::class.java, FalseExpr.serializer(), FalseExpr)
      "hu.bme.mit.theta.core.type.TrueExpr" ->
        TableClass(TrueExpr::class.java, TrueExpr.serializer(), TrueExpr)
      "hu.bme.mit.theta.core.type.BvLitExpr" ->
        TableClass(BvLitExpr::class.java, BvLitExpr.serializer())
      "hu.bme.mit.theta.core.type.EnumLitExpr" ->
        TableClass(EnumLitExpr::class.java, EnumLitExpr.serializer())
      "hu.bme.mit.theta.core.type.FpLitExpr" ->
        TableClass(FpLitExpr::class.java, FpLitExpr.serializer())
      "hu.bme.mit.theta.core.type.FuncLitExpr" ->
        TableClass(
          FuncLitExpr::class.java,
          FuncLitExpr.serializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.IntLitExpr" ->
        TableClass(IntLitExpr::class.java, IntLitExpr.serializer())
      "hu.bme.mit.theta.core.type.InvalidLitExpr" ->
        TableClass(InvalidLitExpr::class.java, InvalidLitExpr.serializer(TypeReferenceSerializer))
      "hu.bme.mit.theta.core.type.RatLitExpr" ->
        TableClass(RatLitExpr::class.java, RatLitExpr.serializer())
      "hu.bme.mit.theta.core.type.BvAddExpr" ->
        TableClass(BvAddExpr::class.java, BvAddExpr.serializer())
      "hu.bme.mit.theta.core.type.FpAddExpr" ->
        TableClass(FpAddExpr::class.java, FpAddExpr.serializer())
      "hu.bme.mit.theta.core.type.IntAddExpr" ->
        TableClass(IntAddExpr::class.java, IntAddExpr.serializer())
      "hu.bme.mit.theta.core.type.RatAddExpr" ->
        TableClass(RatAddExpr::class.java, RatAddExpr.serializer())
      "hu.bme.mit.theta.core.type.AndExpr" -> TableClass(AndExpr::class.java, AndExpr.serializer())
      "hu.bme.mit.theta.core.type.ArrayInitExpr" ->
        TableClass(
          ArrayInitExpr::class.java,
          ArrayInitExpr.serializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.BvAndExpr" ->
        TableClass(BvAndExpr::class.java, BvAndExpr.serializer())
      "hu.bme.mit.theta.core.type.BvOrExpr" ->
        TableClass(BvOrExpr::class.java, BvOrExpr.serializer())
      "hu.bme.mit.theta.core.type.BvXorExpr" ->
        TableClass(BvXorExpr::class.java, BvXorExpr.serializer())
      "hu.bme.mit.theta.core.type.BvMulExpr" ->
        TableClass(BvMulExpr::class.java, BvMulExpr.serializer())
      "hu.bme.mit.theta.core.type.FpMulExpr" ->
        TableClass(FpMulExpr::class.java, FpMulExpr.serializer())
      "hu.bme.mit.theta.core.type.IntMulExpr" ->
        TableClass(IntMulExpr::class.java, IntMulExpr.serializer())
      "hu.bme.mit.theta.core.type.RatMulExpr" ->
        TableClass(RatMulExpr::class.java, RatMulExpr.serializer())
      "hu.bme.mit.theta.core.type.OrExpr" -> TableClass(OrExpr::class.java, OrExpr.serializer())
      "hu.bme.mit.theta.core.type.RefExpr" ->
        TableClass(RefExpr::class.java, RefExpr.serializer(TypeReferenceSerializer))
      "hu.bme.mit.theta.core.type.ExistsExpr" ->
        TableClass(ExistsExpr::class.java, ExistsExpr.serializer())
      "hu.bme.mit.theta.core.type.ForallExpr" ->
        TableClass(ForallExpr::class.java, ForallExpr.serializer())
      "hu.bme.mit.theta.core.type.Reference" ->
        TableClass(
          Reference::class.java,
          Reference.serializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.TraceableWrapperExpr" ->
        TableClass(
          TraceableWrapperExpr::class.java,
          TraceableWrapperExpr.serializer(TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.BvNotExpr" ->
        TableClass(BvNotExpr::class.java, BvNotExpr.serializer())
      "hu.bme.mit.theta.core.type.BvToIntExpr" ->
        TableClass(BvToIntExpr::class.java, BvToIntExpr.serializer())
      "hu.bme.mit.theta.core.type.IntToRatExpr" ->
        TableClass(IntToRatExpr::class.java, IntToRatExpr.serializer())
      "hu.bme.mit.theta.core.type.FpAbsExpr" ->
        TableClass(FpAbsExpr::class.java, FpAbsExpr.serializer())
      "hu.bme.mit.theta.core.type.FpFromBvExpr" ->
        TableClass(FpFromBvExpr::class.java, FpFromBvExpr.serializer())
      "hu.bme.mit.theta.core.type.FpFromIeeeBvExpr" ->
        TableClass(FpFromIeeeBvExpr::class.java, FpFromIeeeBvExpr.serializer())
      "hu.bme.mit.theta.core.type.FpIsInfiniteExpr" ->
        TableClass(FpIsInfiniteExpr::class.java, FpIsInfiniteExpr.serializer())
      "hu.bme.mit.theta.core.type.FpIsNanExpr" ->
        TableClass(FpIsNanExpr::class.java, FpIsNanExpr.serializer())
      "hu.bme.mit.theta.core.type.FpRoundToIntegralExpr" ->
        TableClass(FpRoundToIntegralExpr::class.java, FpRoundToIntegralExpr.serializer())
      "hu.bme.mit.theta.core.type.FpSqrtExpr" ->
        TableClass(FpSqrtExpr::class.java, FpSqrtExpr.serializer())
      "hu.bme.mit.theta.core.type.FpToBvExpr" ->
        TableClass(FpToBvExpr::class.java, FpToBvExpr.serializer())
      "hu.bme.mit.theta.core.type.FpToFpExpr" ->
        TableClass(FpToFpExpr::class.java, FpToFpExpr.serializer())
      "hu.bme.mit.theta.core.type.FpToIeeeBvExpr" ->
        TableClass(FpToIeeeBvExpr::class.java, FpToIeeeBvExpr.serializer())
      "hu.bme.mit.theta.core.type.BvNegExpr" ->
        TableClass(BvNegExpr::class.java, BvNegExpr.serializer())
      "hu.bme.mit.theta.core.type.FpNegExpr" ->
        TableClass(FpNegExpr::class.java, FpNegExpr.serializer())
      "hu.bme.mit.theta.core.type.IntNegExpr" ->
        TableClass(IntNegExpr::class.java, IntNegExpr.serializer())
      "hu.bme.mit.theta.core.type.RatNegExpr" ->
        TableClass(RatNegExpr::class.java, RatNegExpr.serializer())
      "hu.bme.mit.theta.core.type.NotExpr" -> TableClass(NotExpr::class.java, NotExpr.serializer())
      "hu.bme.mit.theta.core.type.BvPosExpr" ->
        TableClass(BvPosExpr::class.java, BvPosExpr.serializer())
      "hu.bme.mit.theta.core.type.BvSignChangeExpr" ->
        TableClass(BvSignChangeExpr::class.java, BvSignChangeExpr.serializer())
      "hu.bme.mit.theta.core.type.FpPosExpr" ->
        TableClass(FpPosExpr::class.java, FpPosExpr.serializer())
      "hu.bme.mit.theta.core.type.IntPosExpr" ->
        TableClass(IntPosExpr::class.java, IntPosExpr.serializer())
      "hu.bme.mit.theta.core.type.RatPosExpr" ->
        TableClass(RatPosExpr::class.java, RatPosExpr.serializer())
      "hu.bme.mit.theta.core.type.PrimeExpr" ->
        TableClass(PrimeExpr::class.java, PrimeExpr.serializer(TypeReferenceSerializer))
      "hu.bme.mit.theta.core.type.RatToIntExpr" ->
        TableClass(RatToIntExpr::class.java, RatToIntExpr.serializer())
      "hu.bme.mit.theta.core.stmt.AssignStmt" ->
        TableClass(AssignStmt::class.java, AssignStmt.serializer(TypeReferenceSerializer))
      "hu.bme.mit.theta.core.stmt.AssumeStmt" ->
        TableClass(AssumeStmt::class.java, AssumeStmt.serializer())
      "hu.bme.mit.theta.core.stmt.HavocStmt" ->
        TableClass(HavocStmt::class.java, HavocStmt.serializer(TypeReferenceSerializer))
      "hu.bme.mit.theta.core.stmt.IfStmt" -> TableClass(IfStmt::class.java, IfStmt.serializer())
      "hu.bme.mit.theta.core.stmt.LoopStmt" ->
        TableClass(LoopStmt::class.java, LoopStmt.serializer())
      "hu.bme.mit.theta.core.stmt.MemoryAssignStmt" ->
        TableClass(
          MemoryAssignStmt::class.java,
          MemoryAssignStmt.serializer(
            TypeReferenceSerializer,
            TypeReferenceSerializer,
            TypeReferenceSerializer,
          ),
        )
      "hu.bme.mit.theta.core.stmt.NonDetStmt" ->
        TableClass(NonDetStmt::class.java, NonDetStmt.serializer())
      "hu.bme.mit.theta.core.stmt.OrtStmt" -> TableClass(OrtStmt::class.java, OrtStmt.serializer())
      "hu.bme.mit.theta.core.stmt.SequenceStmt" ->
        TableClass(SequenceStmt::class.java, SequenceStmt.serializer())
      "hu.bme.mit.theta.core.stmt.SkipStmt" ->
        TableClass(SkipStmt::class.java, SkipStmt.serializer(), SkipStmt)
      "hu.bme.mit.theta.core.decl.BasicConstDecl" ->
        TableClass(
          BasicConstDecl::class.java,
          BasicConstDecl.generatedSerializer(TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.decl.IndexedConstDecl" ->
        TableClass(
          IndexedConstDecl::class.java,
          IndexedConstDecl.generatedSerializer(TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.decl.ParamDecl" ->
        TableClass(ParamDecl::class.java, ParamDecl.generatedSerializer(TypeReferenceSerializer))
      "hu.bme.mit.theta.core.decl.VarDecl" ->
        TableClass(VarDecl::class.java, VarDecl.generatedSerializer(TypeReferenceSerializer))
      "hu.bme.mit.theta.core.type.booltype.BoolType" ->
        TableClass(BoolType::class.java, BoolType.serializer(), BoolType)
      "hu.bme.mit.theta.core.type.inttype.IntType" ->
        TableClass(IntType::class.java, IntType.serializer(), IntType)
      "hu.bme.mit.theta.core.type.rattype.RatType" ->
        TableClass(RatType::class.java, RatType.serializer(), RatType)
      "hu.bme.mit.theta.core.type.bvtype.BvType" ->
        TableClass(BvType::class.java, BvType.generatedSerializer())
      "hu.bme.mit.theta.core.type.fptype.FpType" ->
        TableClass(FpType::class.java, FpType.generatedSerializer())
      "hu.bme.mit.theta.core.type.arraytype.ArrayType" ->
        TableClass(
          ArrayType::class.java,
          ArrayType.generatedSerializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.functype.FuncType" ->
        TableClass(
          FuncType::class.java,
          FuncType.generatedSerializer(TypeReferenceSerializer, TypeReferenceSerializer),
        )
      "hu.bme.mit.theta.core.type.enumtype.EnumType" ->
        TableClass(EnumType::class.java, EnumType.generatedSerializer())
      else -> error("No entry for $name")
    }
}
