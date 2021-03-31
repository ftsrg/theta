; ModuleID = 'dekker.bc'
source_filename = "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/dekker.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%union.pthread_attr_t = type { i64, [48 x i8] }

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1
@.str.1 = private unnamed_addr constant [95 x i8] c"/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/dekker.c\00", align 1
@__PRETTY_FUNCTION__.reach_error = private unnamed_addr constant [19 x i8] c"void reach_error()\00", align 1
@flag1 = dso_local global i32 0, align 4, !dbg !0
@flag2 = dso_local global i32 0, align 4, !dbg !6
@turn = dso_local global i32 0, align 4, !dbg !10
@x = dso_local global i32 0, align 4, !dbg !12

; Function Attrs: nounwind sspstrong uwtable
define dso_local void @assume_abort_if_not(i32 %0) #0 !dbg !20 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4, !tbaa !25
  call void @llvm.dbg.declare(metadata i32* %2, metadata !24, metadata !DIExpression()), !dbg !29
  %3 = load i32, i32* %2, align 4, !dbg !30, !tbaa !25
  %4 = icmp ne i32 %3, 0, !dbg !30
  br i1 %4, label %6, label %5, !dbg !32

5:                                                ; preds = %1
  call void @abort() #7, !dbg !33
  unreachable, !dbg !33

6:                                                ; preds = %1
  ret void, !dbg !35
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: noreturn
declare void @abort() #2

; Function Attrs: nounwind sspstrong uwtable
define dso_local void @reach_error() #0 !dbg !36 {
  call void @__assert_fail(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([95 x i8], [95 x i8]* @.str.1, i64 0, i64 0), i32 7, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @__PRETTY_FUNCTION__.reach_error, i64 0, i64 0)) #8, !dbg !39
  unreachable, !dbg !39
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(i8*, i8*, i32, i8*) #3

; Function Attrs: nounwind sspstrong uwtable
define dso_local i8* @thr1(i8* %0) #0 !dbg !42 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8, !tbaa !50
  call void @llvm.dbg.declare(metadata i8** %2, metadata !47, metadata !DIExpression()), !dbg !52
  store i32 1, i32* @flag1, align 4, !dbg !53, !tbaa !25
  br label %3, !dbg !54

3:                                                ; preds = %15, %1
  %4 = load i32, i32* @flag2, align 4, !dbg !55, !tbaa !25
  %5 = icmp sge i32 %4, 1, !dbg !56
  br i1 %5, label %6, label %16, !dbg !54

6:                                                ; preds = %3
  %7 = load i32, i32* @turn, align 4, !dbg !57, !tbaa !25
  %8 = icmp ne i32 %7, 0, !dbg !60
  br i1 %8, label %9, label %15, !dbg !61

9:                                                ; preds = %6
  store i32 0, i32* @flag1, align 4, !dbg !62, !tbaa !25
  br label %10, !dbg !64

10:                                               ; preds = %13, %9
  %11 = load i32, i32* @turn, align 4, !dbg !65, !tbaa !25
  %12 = icmp ne i32 %11, 0, !dbg !66
  br i1 %12, label %13, label %14, !dbg !64

13:                                               ; preds = %10
  br label %10, !dbg !64, !llvm.loop !67

14:                                               ; preds = %10
  store i32 1, i32* @flag1, align 4, !dbg !70, !tbaa !25
  br label %15, !dbg !71

15:                                               ; preds = %14, %6
  br label %3, !dbg !54, !llvm.loop !72

16:                                               ; preds = %3
  store i32 0, i32* @x, align 4, !dbg !74, !tbaa !25
  %17 = load i32, i32* @x, align 4, !dbg !75, !tbaa !25
  %18 = icmp sle i32 %17, 0, !dbg !75
  br i1 %18, label %21, label %19, !dbg !76

19:                                               ; preds = %16
  br label %20, !dbg !76

20:                                               ; preds = %19
  call void @llvm.dbg.label(metadata !48), !dbg !75
  call void @reach_error(), !dbg !75
  br label %21, !dbg !75

21:                                               ; preds = %20, %16
  store i32 1, i32* @turn, align 4, !dbg !77, !tbaa !25
  store i32 0, i32* @flag1, align 4, !dbg !78, !tbaa !25
  ret i8* null, !dbg !79
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.label(metadata) #1

; Function Attrs: nounwind sspstrong uwtable
define dso_local i8* @thr2(i8* %0) #0 !dbg !80 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8, !tbaa !50
  call void @llvm.dbg.declare(metadata i8** %2, metadata !82, metadata !DIExpression()), !dbg !85
  store i32 1, i32* @flag2, align 4, !dbg !86, !tbaa !25
  br label %3, !dbg !87

3:                                                ; preds = %15, %1
  %4 = load i32, i32* @flag1, align 4, !dbg !88, !tbaa !25
  %5 = icmp sge i32 %4, 1, !dbg !89
  br i1 %5, label %6, label %16, !dbg !87

6:                                                ; preds = %3
  %7 = load i32, i32* @turn, align 4, !dbg !90, !tbaa !25
  %8 = icmp ne i32 %7, 1, !dbg !93
  br i1 %8, label %9, label %15, !dbg !94

9:                                                ; preds = %6
  store i32 0, i32* @flag2, align 4, !dbg !95, !tbaa !25
  br label %10, !dbg !97

10:                                               ; preds = %13, %9
  %11 = load i32, i32* @turn, align 4, !dbg !98, !tbaa !25
  %12 = icmp ne i32 %11, 1, !dbg !99
  br i1 %12, label %13, label %14, !dbg !97

13:                                               ; preds = %10
  br label %10, !dbg !97, !llvm.loop !100

14:                                               ; preds = %10
  store i32 1, i32* @flag2, align 4, !dbg !102, !tbaa !25
  br label %15, !dbg !103

15:                                               ; preds = %14, %6
  br label %3, !dbg !87, !llvm.loop !104

16:                                               ; preds = %3
  store i32 1, i32* @x, align 4, !dbg !106, !tbaa !25
  %17 = load i32, i32* @x, align 4, !dbg !107, !tbaa !25
  %18 = icmp sge i32 %17, 1, !dbg !107
  br i1 %18, label %21, label %19, !dbg !108

19:                                               ; preds = %16
  br label %20, !dbg !108

20:                                               ; preds = %19
  call void @llvm.dbg.label(metadata !83), !dbg !107
  call void @reach_error(), !dbg !107
  br label %21, !dbg !107

21:                                               ; preds = %20, %16
  store i32 1, i32* @turn, align 4, !dbg !109, !tbaa !25
  store i32 0, i32* @flag2, align 4, !dbg !110, !tbaa !25
  ret i8* null, !dbg !111
}

; Function Attrs: nounwind sspstrong uwtable
define dso_local i32 @main() #0 !dbg !112 {
  %1 = alloca i32, align 4
  %2 = alloca i64, align 8
  %3 = alloca i64, align 8
  store i32 0, i32* %1, align 4
  %4 = bitcast i64* %2 to i8*, !dbg !121
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %4) #9, !dbg !121
  call void @llvm.dbg.declare(metadata i64* %2, metadata !116, metadata !DIExpression()), !dbg !122
  %5 = bitcast i64* %3 to i8*, !dbg !121
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %5) #9, !dbg !121
  call void @llvm.dbg.declare(metadata i64* %3, metadata !120, metadata !DIExpression()), !dbg !123
  %6 = load i32, i32* @turn, align 4, !dbg !124, !tbaa !25
  %7 = icmp sle i32 0, %6, !dbg !125
  br i1 %7, label %8, label %11, !dbg !126

8:                                                ; preds = %0
  %9 = load i32, i32* @turn, align 4, !dbg !127, !tbaa !25
  %10 = icmp sle i32 %9, 1, !dbg !128
  br label %11

11:                                               ; preds = %8, %0
  %12 = phi i1 [ false, %0 ], [ %10, %8 ], !dbg !129
  %13 = zext i1 %12 to i32, !dbg !126
  call void @assume_abort_if_not(i32 %13), !dbg !130
  %14 = call i32 @pthread_create(i64* %2, %union.pthread_attr_t* null, i8* (i8*)* @thr1, i8* null) #9, !dbg !131
  %15 = call i32 @pthread_create(i64* %3, %union.pthread_attr_t* null, i8* (i8*)* @thr2, i8* null) #9, !dbg !132
  %16 = load i64, i64* %2, align 8, !dbg !133, !tbaa !134
  %17 = call i32 @pthread_join(i64 %16, i8** null), !dbg !136
  %18 = load i64, i64* %3, align 8, !dbg !137, !tbaa !134
  %19 = call i32 @pthread_join(i64 %18, i8** null), !dbg !138
  %20 = bitcast i64* %3 to i8*, !dbg !139
  call void @llvm.lifetime.end.p0i8(i64 8, i8* %20) #9, !dbg !139
  %21 = bitcast i64* %2 to i8*, !dbg !139
  call void @llvm.lifetime.end.p0i8(i64 8, i8* %21) #9, !dbg !139
  ret i32 0, !dbg !140
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #4

; Function Attrs: nounwind
declare !dbg !141 i32 @pthread_create(i64*, %union.pthread_attr_t*, i8* (i8*)*, i8*) #5

declare !dbg !158 i32 @pthread_join(i64, i8**) #6

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #4

attributes #0 = { nounwind sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }
attributes #2 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { argmemonly nounwind willreturn }
attributes #5 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { noreturn }
attributes #8 = { noreturn nounwind }
attributes #9 = { nounwind }

!llvm.dbg.cu = !{!2}
!llvm.module.flags = !{!14, !15, !16, !17, !18}
!llvm.ident = !{!19}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "flag1", scope: !2, file: !8, line: 16, type: !9, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C99, file: !3, producer: "clang version 11.1.0", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !4, globals: !5, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/dekker.c", directory: "/home/levente/Documents/University/theta")
!4 = !{}
!5 = !{!0, !6, !10, !12}
!6 = !DIGlobalVariableExpression(var: !7, expr: !DIExpression())
!7 = distinct !DIGlobalVariable(name: "flag2", scope: !2, file: !8, line: 16, type: !9, isLocal: false, isDefinition: true)
!8 = !DIFile(filename: "subprojects/xcfa-cli/src/test/resources/llvm/dekker.c", directory: "/home/levente/Documents/University/theta")
!9 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!10 = !DIGlobalVariableExpression(var: !11, expr: !DIExpression())
!11 = distinct !DIGlobalVariable(name: "turn", scope: !2, file: !8, line: 17, type: !9, isLocal: false, isDefinition: true)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(name: "x", scope: !2, file: !8, line: 18, type: !9, isLocal: false, isDefinition: true)
!14 = !{i32 7, !"Dwarf Version", i32 4}
!15 = !{i32 2, !"Debug Info Version", i32 3}
!16 = !{i32 1, !"wchar_size", i32 4}
!17 = !{i32 7, !"PIC Level", i32 2}
!18 = !{i32 7, !"PIE Level", i32 2}
!19 = !{!"clang version 11.1.0"}
!20 = distinct !DISubprogram(name: "assume_abort_if_not", scope: !8, file: !8, line: 2, type: !21, scopeLine: 2, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !23)
!21 = !DISubroutineType(types: !22)
!22 = !{null, !9}
!23 = !{!24}
!24 = !DILocalVariable(name: "cond", arg: 1, scope: !20, file: !8, line: 2, type: !9)
!25 = !{!26, !26, i64 0}
!26 = !{!"int", !27, i64 0}
!27 = !{!"omnipotent char", !28, i64 0}
!28 = !{!"Simple C/C++ TBAA"}
!29 = !DILocation(line: 2, column: 30, scope: !20)
!30 = !DILocation(line: 3, column: 7, scope: !31)
!31 = distinct !DILexicalBlock(scope: !20, file: !8, line: 3, column: 6)
!32 = !DILocation(line: 3, column: 6, scope: !20)
!33 = !DILocation(line: 3, column: 14, scope: !34)
!34 = distinct !DILexicalBlock(scope: !31, file: !8, line: 3, column: 13)
!35 = !DILocation(line: 4, column: 1, scope: !20)
!36 = distinct !DISubprogram(name: "reach_error", scope: !8, file: !8, line: 7, type: !37, scopeLine: 7, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !4)
!37 = !DISubroutineType(types: !38)
!38 = !{null}
!39 = !DILocation(line: 7, column: 22, scope: !40)
!40 = distinct !DILexicalBlock(scope: !41, file: !8, line: 7, column: 22)
!41 = distinct !DILexicalBlock(scope: !36, file: !8, line: 7, column: 22)
!42 = distinct !DISubprogram(name: "thr1", scope: !8, file: !8, line: 20, type: !43, scopeLine: 20, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !46)
!43 = !DISubroutineType(types: !44)
!44 = !{!45, !45}
!45 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!46 = !{!47, !48}
!47 = !DILocalVariable(name: "_", arg: 1, scope: !42, file: !8, line: 20, type: !45)
!48 = !DILabel(scope: !49, name: "ERROR", file: !8, line: 31)
!49 = distinct !DILexicalBlock(scope: !42, file: !8, line: 31, column: 3)
!50 = !{!51, !51, i64 0}
!51 = !{!"any pointer", !27, i64 0}
!52 = !DILocation(line: 20, column: 18, scope: !42)
!53 = !DILocation(line: 21, column: 9, scope: !42)
!54 = !DILocation(line: 22, column: 3, scope: !42)
!55 = !DILocation(line: 22, column: 10, scope: !42)
!56 = !DILocation(line: 22, column: 16, scope: !42)
!57 = !DILocation(line: 23, column: 9, scope: !58)
!58 = distinct !DILexicalBlock(scope: !59, file: !8, line: 23, column: 9)
!59 = distinct !DILexicalBlock(scope: !42, file: !8, line: 22, column: 22)
!60 = !DILocation(line: 23, column: 14, scope: !58)
!61 = !DILocation(line: 23, column: 9, scope: !59)
!62 = !DILocation(line: 24, column: 13, scope: !63)
!63 = distinct !DILexicalBlock(scope: !58, file: !8, line: 23, column: 20)
!64 = !DILocation(line: 25, column: 7, scope: !63)
!65 = !DILocation(line: 25, column: 14, scope: !63)
!66 = !DILocation(line: 25, column: 19, scope: !63)
!67 = distinct !{!67, !64, !68, !69}
!68 = !DILocation(line: 25, column: 26, scope: !63)
!69 = !{!"llvm.loop.unroll.disable"}
!70 = !DILocation(line: 26, column: 13, scope: !63)
!71 = !DILocation(line: 27, column: 5, scope: !63)
!72 = distinct !{!72, !54, !73, !69}
!73 = !DILocation(line: 28, column: 3, scope: !42)
!74 = !DILocation(line: 30, column: 5, scope: !42)
!75 = !DILocation(line: 31, column: 3, scope: !49)
!76 = !DILocation(line: 31, column: 3, scope: !42)
!77 = !DILocation(line: 33, column: 8, scope: !42)
!78 = !DILocation(line: 34, column: 9, scope: !42)
!79 = !DILocation(line: 35, column: 3, scope: !42)
!80 = distinct !DISubprogram(name: "thr2", scope: !8, file: !8, line: 38, type: !43, scopeLine: 38, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !81)
!81 = !{!82, !83}
!82 = !DILocalVariable(name: "_", arg: 1, scope: !80, file: !8, line: 38, type: !45)
!83 = !DILabel(scope: !84, name: "ERROR", file: !8, line: 49)
!84 = distinct !DILexicalBlock(scope: !80, file: !8, line: 49, column: 3)
!85 = !DILocation(line: 38, column: 18, scope: !80)
!86 = !DILocation(line: 39, column: 9, scope: !80)
!87 = !DILocation(line: 40, column: 3, scope: !80)
!88 = !DILocation(line: 40, column: 10, scope: !80)
!89 = !DILocation(line: 40, column: 16, scope: !80)
!90 = !DILocation(line: 41, column: 9, scope: !91)
!91 = distinct !DILexicalBlock(scope: !92, file: !8, line: 41, column: 9)
!92 = distinct !DILexicalBlock(scope: !80, file: !8, line: 40, column: 22)
!93 = !DILocation(line: 41, column: 14, scope: !91)
!94 = !DILocation(line: 41, column: 9, scope: !92)
!95 = !DILocation(line: 42, column: 13, scope: !96)
!96 = distinct !DILexicalBlock(scope: !91, file: !8, line: 41, column: 20)
!97 = !DILocation(line: 43, column: 7, scope: !96)
!98 = !DILocation(line: 43, column: 14, scope: !96)
!99 = !DILocation(line: 43, column: 19, scope: !96)
!100 = distinct !{!100, !97, !101, !69}
!101 = !DILocation(line: 43, column: 26, scope: !96)
!102 = !DILocation(line: 44, column: 13, scope: !96)
!103 = !DILocation(line: 45, column: 5, scope: !96)
!104 = distinct !{!104, !87, !105, !69}
!105 = !DILocation(line: 46, column: 3, scope: !80)
!106 = !DILocation(line: 48, column: 5, scope: !80)
!107 = !DILocation(line: 49, column: 3, scope: !84)
!108 = !DILocation(line: 49, column: 3, scope: !80)
!109 = !DILocation(line: 51, column: 8, scope: !80)
!110 = !DILocation(line: 52, column: 9, scope: !80)
!111 = !DILocation(line: 53, column: 3, scope: !80)
!112 = distinct !DISubprogram(name: "main", scope: !8, file: !8, line: 56, type: !113, scopeLine: 56, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !115)
!113 = !DISubroutineType(types: !114)
!114 = !{!9}
!115 = !{!116, !120}
!116 = !DILocalVariable(name: "t1", scope: !112, file: !8, line: 57, type: !117)
!117 = !DIDerivedType(tag: DW_TAG_typedef, name: "pthread_t", file: !118, line: 27, baseType: !119)
!118 = !DIFile(filename: "/usr/include/bits/pthreadtypes.h", directory: "")
!119 = !DIBasicType(name: "long unsigned int", size: 64, encoding: DW_ATE_unsigned)
!120 = !DILocalVariable(name: "t2", scope: !112, file: !8, line: 57, type: !117)
!121 = !DILocation(line: 57, column: 3, scope: !112)
!122 = !DILocation(line: 57, column: 13, scope: !112)
!123 = !DILocation(line: 57, column: 17, scope: !112)
!124 = !DILocation(line: 58, column: 26, scope: !112)
!125 = !DILocation(line: 58, column: 24, scope: !112)
!126 = !DILocation(line: 58, column: 31, scope: !112)
!127 = !DILocation(line: 58, column: 34, scope: !112)
!128 = !DILocation(line: 58, column: 38, scope: !112)
!129 = !DILocation(line: 0, scope: !112)
!130 = !DILocation(line: 58, column: 3, scope: !112)
!131 = !DILocation(line: 59, column: 3, scope: !112)
!132 = !DILocation(line: 60, column: 3, scope: !112)
!133 = !DILocation(line: 61, column: 16, scope: !112)
!134 = !{!135, !135, i64 0}
!135 = !{!"long", !27, i64 0}
!136 = !DILocation(line: 61, column: 3, scope: !112)
!137 = !DILocation(line: 62, column: 16, scope: !112)
!138 = !DILocation(line: 62, column: 3, scope: !112)
!139 = !DILocation(line: 64, column: 1, scope: !112)
!140 = !DILocation(line: 63, column: 3, scope: !112)
!141 = !DISubprogram(name: "pthread_create", scope: !142, file: !142, line: 200, type: !143, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !4)
!142 = !DIFile(filename: "/usr/include/pthread.h", directory: "")
!143 = !DISubroutineType(types: !144)
!144 = !{!9, !145, !146, !157, !45}
!145 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !119, size: 64)
!146 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !147, size: 64)
!147 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !148)
!148 = distinct !DICompositeType(tag: DW_TAG_union_type, name: "pthread_attr_t", file: !118, line: 56, size: 448, elements: !149)
!149 = !{!150, !155}
!150 = !DIDerivedType(tag: DW_TAG_member, name: "__size", scope: !148, file: !118, line: 58, baseType: !151, size: 448)
!151 = !DICompositeType(tag: DW_TAG_array_type, baseType: !152, size: 448, elements: !153)
!152 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!153 = !{!154}
!154 = !DISubrange(count: 56)
!155 = !DIDerivedType(tag: DW_TAG_member, name: "__align", scope: !148, file: !118, line: 59, baseType: !156, size: 64)
!156 = !DIBasicType(name: "long int", size: 64, encoding: DW_ATE_signed)
!157 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !43, size: 64)
!158 = !DISubprogram(name: "pthread_join", scope: !142, file: !142, line: 217, type: !159, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !4)
!159 = !DISubroutineType(types: !160)
!160 = !{!9, !119, !161}
!161 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !45, size: 64)
