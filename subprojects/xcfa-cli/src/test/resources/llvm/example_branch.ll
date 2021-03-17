; ModuleID = 'example_branch.bc'
source_filename = "example_branch.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @main() #0 !dbg !9 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !13, metadata !DIExpression()), !dbg !14
  store i32 0, i32* %2, align 4, !dbg !14
  %3 = load i32, i32* %2, align 4, !dbg !15
  %4 = icmp sgt i32 %3, 0, !dbg !17
  br i1 %4, label %5, label %6, !dbg !18

5:                                                ; preds = %0
  store i32 0, i32* %2, align 4, !dbg !19
  br label %6, !dbg !21

6:                                                ; preds = %5, %0
  ret i32 0, !dbg !22
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6, !7}
!llvm.ident = !{!8}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 11.1.0", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "example_branch.c", directory: "/home/solarowl/Research/Protos/xcfa-ir-proto/jni_library/examples")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{i32 7, !"PIE Level", i32 2}
!8 = !{!"clang version 11.1.0"}
!9 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 1, type: !10, scopeLine: 1, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!10 = !DISubroutineType(types: !11)
!11 = !{!12}
!12 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!13 = !DILocalVariable(name: "a", scope: !9, file: !1, line: 2, type: !12)
!14 = !DILocation(line: 2, column: 9, scope: !9)
!15 = !DILocation(line: 3, column: 8, scope: !16)
!16 = distinct !DILexicalBlock(scope: !9, file: !1, line: 3, column: 8)
!17 = !DILocation(line: 3, column: 9, scope: !16)
!18 = !DILocation(line: 3, column: 8, scope: !9)
!19 = !DILocation(line: 4, column: 10, scope: !20)
!20 = distinct !DILexicalBlock(scope: !16, file: !1, line: 3, column: 13)
!21 = !DILocation(line: 5, column: 5, scope: !20)
!22 = !DILocation(line: 6, column: 5, scope: !9)
