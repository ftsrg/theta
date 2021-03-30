; ModuleID = '/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/test_locks_10.bc'
source_filename = "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/test_locks_10.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1
@.str.1 = private unnamed_addr constant [16 x i8] c"test_locks_10.c\00", align 1
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(i8*, i8*, i32, i8*) #0

; Function Attrs: nounwind sspstrong uwtable
define dso_local i32 @main() #1 !dbg !9 {
  %1 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !38
  call void @llvm.dbg.value(metadata i32 %1, metadata !15, metadata !DIExpression()), !dbg !39
  %2 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !40
  call void @llvm.dbg.value(metadata i32 %2, metadata !17, metadata !DIExpression()), !dbg !39
  %3 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !41
  call void @llvm.dbg.value(metadata i32 %3, metadata !19, metadata !DIExpression()), !dbg !39
  %4 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !42
  call void @llvm.dbg.value(metadata i32 %4, metadata !21, metadata !DIExpression()), !dbg !39
  %5 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !43
  call void @llvm.dbg.value(metadata i32 %5, metadata !23, metadata !DIExpression()), !dbg !39
  %6 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !44
  call void @llvm.dbg.value(metadata i32 %6, metadata !25, metadata !DIExpression()), !dbg !39
  %7 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !45
  call void @llvm.dbg.value(metadata i32 %7, metadata !27, metadata !DIExpression()), !dbg !39
  %8 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !46
  call void @llvm.dbg.value(metadata i32 %8, metadata !29, metadata !DIExpression()), !dbg !39
  %9 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !47
  call void @llvm.dbg.value(metadata i32 %9, metadata !31, metadata !DIExpression()), !dbg !39
  %10 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !48
  call void @llvm.dbg.value(metadata i32 %10, metadata !33, metadata !DIExpression()), !dbg !39
  br label %11, !dbg !49

11:                                               ; preds = %14, %0
  %12 = call i32 (...) @__VERIFIER_nondet_int() #6, !dbg !50
  call void @llvm.dbg.value(metadata i32 %12, metadata !35, metadata !DIExpression()), !dbg !39
  %13 = icmp eq i32 %12, 0, !dbg !52
  br i1 %13, label %15, label %14, !dbg !54

14:                                               ; preds = %11
  call void @llvm.dbg.value(metadata i32 0, metadata !16, metadata !DIExpression()), !dbg !39
  call void @llvm.dbg.value(metadata i32 0, metadata !18, metadata !DIExpression()), !dbg !39
  call void @llvm.dbg.value(metadata i32 0, metadata !20, metadata !DIExpression()), !dbg !39
  call void @llvm.dbg.value(metadata i32 0, metadata !22, metadata !DIExpression()), !dbg !39
  call void @llvm.dbg.value(metadata i32 0, metadata !24, metadata !DIExpression()), !dbg !39
  call void @llvm.dbg.value(metadata i32 0, metadata !26, metadata !DIExpression()), !dbg !39
  call void @llvm.dbg.value(metadata i32 0, metadata !28, metadata !DIExpression()), !dbg !39
  call void @llvm.dbg.value(metadata i32 0, metadata !30, metadata !DIExpression()), !dbg !39
  call void @llvm.dbg.value(metadata i32 0, metadata !32, metadata !DIExpression()), !dbg !39
  call void @llvm.dbg.value(metadata i32 0, metadata !34, metadata !DIExpression()), !dbg !39
  %.not = icmp eq i32 %1, 0, !dbg !55
  %. = select i1 %.not, i1 false, i1 true
  call void @llvm.dbg.value(metadata i32 undef, metadata !16, metadata !DIExpression()), !dbg !39
  %.not10 = icmp eq i32 %2, 0, !dbg !57
  %.not37 = select i1 %.not10, i1 false, i1 true, !dbg !59
  call void @llvm.dbg.value(metadata i32 undef, metadata !18, metadata !DIExpression()), !dbg !39
  %.not11 = icmp eq i32 %3, 0, !dbg !60
  %.39 = select i1 %.not11, i1 false, i1 true
  call void @llvm.dbg.value(metadata i32 undef, metadata !20, metadata !DIExpression()), !dbg !39
  %.not12 = icmp eq i32 %4, 0, !dbg !62
  %.not35 = select i1 %.not12, i1 false, i1 true, !dbg !64
  call void @llvm.dbg.value(metadata i32 undef, metadata !22, metadata !DIExpression()), !dbg !39
  %.not13 = icmp eq i32 %5, 0, !dbg !65
  %.40 = select i1 %.not13, i1 false, i1 true
  call void @llvm.dbg.value(metadata i32 undef, metadata !24, metadata !DIExpression()), !dbg !39
  %.not14 = icmp eq i32 %6, 0, !dbg !67
  %.not33 = select i1 %.not14, i1 false, i1 true, !dbg !69
  call void @llvm.dbg.value(metadata i32 undef, metadata !26, metadata !DIExpression()), !dbg !39
  %.not15 = icmp eq i32 %7, 0, !dbg !70
  %.41 = select i1 %.not15, i1 false, i1 true
  call void @llvm.dbg.value(metadata i32 undef, metadata !28, metadata !DIExpression()), !dbg !39
  %.not16 = icmp eq i32 %8, 0, !dbg !72
  %.not31 = select i1 %.not16, i1 false, i1 true, !dbg !74
  call void @llvm.dbg.value(metadata i32 undef, metadata !30, metadata !DIExpression()), !dbg !39
  %.not17 = icmp eq i32 %9, 0, !dbg !75
  %.42 = select i1 %.not17, i1 false, i1 true
  call void @llvm.dbg.value(metadata i32 undef, metadata !32, metadata !DIExpression()), !dbg !39
  %.not18 = icmp eq i32 %10, 0, !dbg !77
  %.not29 = select i1 %.not18, i1 false, i1 true, !dbg !79
  call void @llvm.dbg.value(metadata i32 undef, metadata !34, metadata !DIExpression()), !dbg !39
  %.not19 = icmp eq i32 %1, 0, !dbg !80
  %brmerge = or i1 %.not19, %., !dbg !82
  %.not20 = icmp eq i32 %2, 0
  %brmerge43 = or i1 %.not20, %.not37
  %or.cond = and i1 %brmerge, %brmerge43, !dbg !82
  %.not21 = icmp eq i32 %3, 0
  %brmerge44 = or i1 %.not21, %.39
  %or.cond52 = and i1 %or.cond, %brmerge44, !dbg !82
  %.not22 = icmp eq i32 %4, 0
  %brmerge45 = or i1 %.not22, %.not35
  %or.cond53 = and i1 %or.cond52, %brmerge45, !dbg !82
  %.not23 = icmp eq i32 %5, 0
  %brmerge46 = or i1 %.not23, %.40
  %or.cond54 = and i1 %or.cond53, %brmerge46, !dbg !82
  %.not24 = icmp eq i32 %6, 0
  %brmerge47 = or i1 %.not24, %.not33
  %or.cond55 = and i1 %or.cond54, %brmerge47, !dbg !82
  %.not25 = icmp eq i32 %7, 0
  %brmerge48 = or i1 %.not25, %.41
  %or.cond56 = and i1 %or.cond55, %brmerge48, !dbg !82
  %.not26 = icmp eq i32 %8, 0
  %brmerge49 = or i1 %.not26, %.not31
  %or.cond57 = and i1 %or.cond56, %brmerge49, !dbg !82
  %.not27 = icmp eq i32 %9, 0
  %brmerge50 = or i1 %.not27, %.42
  %or.cond58 = and i1 %or.cond57, %brmerge50, !dbg !82
  %.not28 = icmp eq i32 %10, 0
  %brmerge51 = or i1 %.not28, %.not29
  %or.cond59 = and i1 %or.cond58, %brmerge51, !dbg !82
  br i1 %or.cond59, label %11, label %16, !dbg !82, !llvm.loop !83

15:                                               ; preds = %11
  call void @llvm.dbg.label(metadata !36), !dbg !86
  ret i32 0, !dbg !87

16:                                               ; preds = %14
  call void @llvm.dbg.label(metadata !37), !dbg !88
  call void @__assert_fail(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([16 x i8], [16 x i8]* @.str.1, i64 0, i64 0), i32 3, i8* getelementptr inbounds ([12 x i8], [12 x i8]* @.str.2, i64 0, i64 0)) #7, !dbg !89
  unreachable, !dbg !89
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #2

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #3

declare i32 @__VERIFIER_nondet_int(...) #4

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.label(metadata) #3

; Function Attrs: noreturn
declare void @abort() #5

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #2

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.value(metadata, metadata, metadata) #3

attributes #0 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { argmemonly nounwind willreturn }
attributes #3 = { nounwind readnone speculatable willreturn }
attributes #4 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { nounwind }
attributes #7 = { noreturn nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6, !7}
!llvm.ident = !{!8}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 11.1.0", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/test_locks_10.c", directory: "/home/levente/Documents/University/theta")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{i32 7, !"PIE Level", i32 2}
!8 = !{!"clang version 11.1.0"}
!9 = distinct !DISubprogram(name: "main", scope: !10, file: !10, line: 6, type: !11, scopeLine: 7, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !14)
!10 = !DIFile(filename: "subprojects/xcfa-cli/src/test/resources/llvm/test_locks_10.c", directory: "/home/levente/Documents/University/theta")
!11 = !DISubroutineType(types: !12)
!12 = !{!13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{!15, !16, !17, !18, !19, !20, !21, !22, !23, !24, !25, !26, !27, !28, !29, !30, !31, !32, !33, !34, !35, !36, !37}
!15 = !DILocalVariable(name: "p1", scope: !9, file: !10, line: 8, type: !13)
!16 = !DILocalVariable(name: "lk1", scope: !9, file: !10, line: 9, type: !13)
!17 = !DILocalVariable(name: "p2", scope: !9, file: !10, line: 11, type: !13)
!18 = !DILocalVariable(name: "lk2", scope: !9, file: !10, line: 12, type: !13)
!19 = !DILocalVariable(name: "p3", scope: !9, file: !10, line: 14, type: !13)
!20 = !DILocalVariable(name: "lk3", scope: !9, file: !10, line: 15, type: !13)
!21 = !DILocalVariable(name: "p4", scope: !9, file: !10, line: 17, type: !13)
!22 = !DILocalVariable(name: "lk4", scope: !9, file: !10, line: 18, type: !13)
!23 = !DILocalVariable(name: "p5", scope: !9, file: !10, line: 20, type: !13)
!24 = !DILocalVariable(name: "lk5", scope: !9, file: !10, line: 21, type: !13)
!25 = !DILocalVariable(name: "p6", scope: !9, file: !10, line: 23, type: !13)
!26 = !DILocalVariable(name: "lk6", scope: !9, file: !10, line: 24, type: !13)
!27 = !DILocalVariable(name: "p7", scope: !9, file: !10, line: 26, type: !13)
!28 = !DILocalVariable(name: "lk7", scope: !9, file: !10, line: 27, type: !13)
!29 = !DILocalVariable(name: "p8", scope: !9, file: !10, line: 29, type: !13)
!30 = !DILocalVariable(name: "lk8", scope: !9, file: !10, line: 30, type: !13)
!31 = !DILocalVariable(name: "p9", scope: !9, file: !10, line: 32, type: !13)
!32 = !DILocalVariable(name: "lk9", scope: !9, file: !10, line: 33, type: !13)
!33 = !DILocalVariable(name: "p10", scope: !9, file: !10, line: 35, type: !13)
!34 = !DILocalVariable(name: "lk10", scope: !9, file: !10, line: 36, type: !13)
!35 = !DILocalVariable(name: "cond", scope: !9, file: !10, line: 39, type: !13)
!36 = !DILabel(scope: !9, name: "out", file: !10, line: 161)
!37 = !DILabel(scope: !9, name: "ERROR", file: !10, line: 163)
!38 = !DILocation(line: 8, column: 14, scope: !9)
!39 = !DILocation(line: 0, scope: !9)
!40 = !DILocation(line: 11, column: 14, scope: !9)
!41 = !DILocation(line: 14, column: 14, scope: !9)
!42 = !DILocation(line: 17, column: 14, scope: !9)
!43 = !DILocation(line: 20, column: 14, scope: !9)
!44 = !DILocation(line: 23, column: 14, scope: !9)
!45 = !DILocation(line: 26, column: 14, scope: !9)
!46 = !DILocation(line: 29, column: 14, scope: !9)
!47 = !DILocation(line: 32, column: 14, scope: !9)
!48 = !DILocation(line: 35, column: 15, scope: !9)
!49 = !DILocation(line: 41, column: 5, scope: !9)
!50 = !DILocation(line: 42, column: 16, scope: !51)
!51 = distinct !DILexicalBlock(scope: !9, file: !10, line: 41, column: 14)
!52 = !DILocation(line: 43, column: 18, scope: !53)
!53 = distinct !DILexicalBlock(scope: !51, file: !10, line: 43, column: 13)
!54 = !DILocation(line: 43, column: 13, scope: !51)
!55 = !DILocation(line: 68, column: 16, scope: !56)
!56 = distinct !DILexicalBlock(scope: !51, file: !10, line: 68, column: 13)
!57 = !DILocation(line: 72, column: 16, scope: !58)
!58 = distinct !DILexicalBlock(scope: !51, file: !10, line: 72, column: 13)
!59 = !DILocation(line: 72, column: 13, scope: !51)
!60 = !DILocation(line: 76, column: 16, scope: !61)
!61 = distinct !DILexicalBlock(scope: !51, file: !10, line: 76, column: 13)
!62 = !DILocation(line: 80, column: 16, scope: !63)
!63 = distinct !DILexicalBlock(scope: !51, file: !10, line: 80, column: 13)
!64 = !DILocation(line: 80, column: 13, scope: !51)
!65 = !DILocation(line: 84, column: 16, scope: !66)
!66 = distinct !DILexicalBlock(scope: !51, file: !10, line: 84, column: 13)
!67 = !DILocation(line: 88, column: 16, scope: !68)
!68 = distinct !DILexicalBlock(scope: !51, file: !10, line: 88, column: 13)
!69 = !DILocation(line: 88, column: 13, scope: !51)
!70 = !DILocation(line: 92, column: 16, scope: !71)
!71 = distinct !DILexicalBlock(scope: !51, file: !10, line: 92, column: 13)
!72 = !DILocation(line: 96, column: 16, scope: !73)
!73 = distinct !DILexicalBlock(scope: !51, file: !10, line: 96, column: 13)
!74 = !DILocation(line: 96, column: 13, scope: !51)
!75 = !DILocation(line: 100, column: 16, scope: !76)
!76 = distinct !DILexicalBlock(scope: !51, file: !10, line: 100, column: 13)
!77 = !DILocation(line: 104, column: 17, scope: !78)
!78 = distinct !DILexicalBlock(scope: !51, file: !10, line: 104, column: 13)
!79 = !DILocation(line: 104, column: 13, scope: !51)
!80 = !DILocation(line: 110, column: 16, scope: !81)
!81 = distinct !DILexicalBlock(scope: !51, file: !10, line: 110, column: 13)
!82 = !DILocation(line: 110, column: 13, scope: !51)
!83 = distinct !{!83, !49, !84, !85}
!84 = !DILocation(line: 160, column: 5, scope: !9)
!85 = !{!"llvm.loop.unroll.disable"}
!86 = !DILocation(line: 161, column: 3, scope: !9)
!87 = !DILocation(line: 162, column: 5, scope: !9)
!88 = !DILocation(line: 163, column: 3, scope: !9)
!89 = !DILocation(line: 3, column: 22, scope: !90, inlinedAt: !93)
!90 = distinct !DISubprogram(name: "reach_error", scope: !10, file: !10, line: 3, type: !91, scopeLine: 3, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !2)
!91 = !DISubroutineType(types: !92)
!92 = !{null}
!93 = distinct !DILocation(line: 163, column: 11, scope: !94)
!94 = distinct !DILexicalBlock(scope: !9, file: !10, line: 163, column: 10)
