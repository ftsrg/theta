; ModuleID = '/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/example_addition.bc'
source_filename = "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/example_addition.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: nounwind sspstrong uwtable
define dso_local i32 @main() local_unnamed_addr #0 !dbg !9 {
  %1 = alloca float, align 4
  %2 = alloca double, align 8
  %.0.sroa_cast3 = bitcast float* %1 to i8*, !dbg !22
  call void @llvm.lifetime.start.p0i8(i64 4, i8* nonnull %.0.sroa_cast3), !dbg !22
  call void @llvm.dbg.declare(metadata float* %1, metadata !15, metadata !DIExpression()), !dbg !23
  store volatile float 2.000000e+00, float* %1, align 4, !dbg !23, !tbaa !24
  %.0.sroa_cast = bitcast double* %2 to i8*, !dbg !28
  call void @llvm.lifetime.start.p0i8(i64 8, i8* nonnull %.0.sroa_cast), !dbg !28
  call void @llvm.dbg.declare(metadata double* %2, metadata !18, metadata !DIExpression()), !dbg !29
  store volatile double 3.000000e+00, double* %2, align 8, !dbg !29, !tbaa !30
  %.0.2 = load volatile float, float* %1, align 4, !dbg !32, !tbaa !24
  %3 = fpext float %.0.2 to double, !dbg !32
  %.0. = load volatile double, double* %2, align 8, !dbg !33, !tbaa !30
  %4 = fadd double %.0., %3, !dbg !34
  %5 = fptosi double %4 to i32, !dbg !32
  call void @llvm.dbg.value(metadata i32 %5, metadata !21, metadata !DIExpression()), !dbg !35
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %.0.sroa_cast), !dbg !36
  call void @llvm.lifetime.end.p0i8(i64 4, i8* nonnull %.0.sroa_cast3), !dbg !36
  ret i32 %5, !dbg !37
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #2

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.value(metadata, metadata, metadata) #2

declare void @setArrayElement(void, void, void)

attributes #0 = { nounwind sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind willreturn }
attributes #2 = { nounwind readnone speculatable willreturn }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6, !7}
!llvm.ident = !{!8}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 11.1.0", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/example_addition.c", directory: "/home/levente/Documents/University/theta")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{i32 7, !"PIE Level", i32 2}
!8 = !{!"clang version 11.1.0"}
!9 = distinct !DISubprogram(name: "main", scope: !10, file: !10, line: 1, type: !11, scopeLine: 1, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !14)
!10 = !DIFile(filename: "subprojects/xcfa-cli/src/test/resources/llvm/example_addition.c", directory: "/home/levente/Documents/University/theta")
!11 = !DISubroutineType(types: !12)
!12 = !{!13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{!15, !18, !21}
!15 = !DILocalVariable(name: "a", scope: !9, file: !10, line: 2, type: !16)
!16 = !DIDerivedType(tag: DW_TAG_volatile_type, baseType: !17)
!17 = !DIBasicType(name: "float", size: 32, encoding: DW_ATE_float)
!18 = !DILocalVariable(name: "b", scope: !9, file: !10, line: 3, type: !19)
!19 = !DIDerivedType(tag: DW_TAG_volatile_type, baseType: !20)
!20 = !DIBasicType(name: "double", size: 64, encoding: DW_ATE_float)
!21 = !DILocalVariable(name: "c", scope: !9, file: !10, line: 4, type: !13)
!22 = !DILocation(line: 2, column: 5, scope: !9)
!23 = !DILocation(line: 2, column: 20, scope: !9)
!24 = !{!25, !25, i64 0}
!25 = !{!"float", !26, i64 0}
!26 = !{!"omnipotent char", !27, i64 0}
!27 = !{!"Simple C/C++ TBAA"}
!28 = !DILocation(line: 3, column: 5, scope: !9)
!29 = !DILocation(line: 3, column: 21, scope: !9)
!30 = !{!31, !31, i64 0}
!31 = !{!"double", !26, i64 0}
!32 = !DILocation(line: 4, column: 13, scope: !9)
!33 = !DILocation(line: 4, column: 15, scope: !9)
!34 = !DILocation(line: 4, column: 14, scope: !9)
!35 = !DILocation(line: 0, scope: !9)
!36 = !DILocation(line: 6, column: 1, scope: !9)
!37 = !DILocation(line: 5, column: 5, scope: !9)
