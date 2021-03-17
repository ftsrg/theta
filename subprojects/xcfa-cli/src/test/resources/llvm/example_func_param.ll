; ModuleID = 'example_func_param.bc'
source_filename = "example_func_param.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @adder(i32 %0, i32 %1) #0 !dbg !9 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !13, metadata !DIExpression()), !dbg !14
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !15, metadata !DIExpression()), !dbg !16
  call void @llvm.dbg.declare(metadata i32* %5, metadata !17, metadata !DIExpression()), !dbg !18
  %7 = load i32, i32* %3, align 4, !dbg !19
  store i32 %7, i32* %5, align 4, !dbg !18
  call void @llvm.dbg.declare(metadata i32* %6, metadata !20, metadata !DIExpression()), !dbg !21
  %8 = load i32, i32* %4, align 4, !dbg !22
  store i32 %8, i32* %6, align 4, !dbg !21
  %9 = load i32, i32* %5, align 4, !dbg !23
  %10 = load i32, i32* %6, align 4, !dbg !24
  %11 = add nsw i32 %9, %10, !dbg !25
  ret i32 %11, !dbg !26
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @main() #0 !dbg !27 {
  %1 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  %2 = call i32 @adder(i32 2, i32 -2), !dbg !30
  ret i32 %2, !dbg !31
}

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6, !7}
!llvm.ident = !{!8}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 11.1.0", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "example_func_param.c", directory: "/home/solarowl/Research/Protos/xcfa-ir-proto/jni_library/examples")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{i32 7, !"PIE Level", i32 2}
!8 = !{!"clang version 11.1.0"}
!9 = distinct !DISubprogram(name: "adder", scope: !1, file: !1, line: 1, type: !10, scopeLine: 1, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!10 = !DISubroutineType(types: !11)
!11 = !{!12, !12, !12}
!12 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!13 = !DILocalVariable(name: "a", arg: 1, scope: !9, file: !1, line: 1, type: !12)
!14 = !DILocation(line: 1, column: 15, scope: !9)
!15 = !DILocalVariable(name: "b", arg: 2, scope: !9, file: !1, line: 1, type: !12)
!16 = !DILocation(line: 1, column: 22, scope: !9)
!17 = !DILocalVariable(name: "c", scope: !9, file: !1, line: 2, type: !12)
!18 = !DILocation(line: 2, column: 9, scope: !9)
!19 = !DILocation(line: 2, column: 13, scope: !9)
!20 = !DILocalVariable(name: "d", scope: !9, file: !1, line: 2, type: !12)
!21 = !DILocation(line: 2, column: 20, scope: !9)
!22 = !DILocation(line: 2, column: 24, scope: !9)
!23 = !DILocation(line: 3, column: 12, scope: !9)
!24 = !DILocation(line: 3, column: 14, scope: !9)
!25 = !DILocation(line: 3, column: 13, scope: !9)
!26 = !DILocation(line: 3, column: 5, scope: !9)
!27 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 6, type: !28, scopeLine: 6, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!28 = !DISubroutineType(types: !29)
!29 = !{!12}
!30 = !DILocation(line: 7, column: 12, scope: !27)
!31 = !DILocation(line: 7, column: 5, scope: !27)
