; ModuleID = '/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/dekker.bc'
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
define dso_local void @assume_abort_if_not(i32 %0) #0 !dbg !21 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !25, metadata !DIExpression()), !dbg !26
  %.not = icmp eq i32 %0, 0, !dbg !27
  br i1 %.not, label %2, label %3, !dbg !29

2:                                                ; preds = %1
  call void @abort() #7, !dbg !30
  unreachable, !dbg !30

3:                                                ; preds = %1
  ret void, !dbg !32
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: noreturn
declare void @abort() #2

; Function Attrs: nounwind sspstrong uwtable
define dso_local void @reach_error() #0 !dbg !33 {
  call void @__assert_fail(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([95 x i8], [95 x i8]* @.str.1, i64 0, i64 0), i32 7, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @__PRETTY_FUNCTION__.reach_error, i64 0, i64 0)) #7, !dbg !36
  unreachable, !dbg !36
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(i8*, i8*, i32, i8*) #3

; Function Attrs: nounwind sspstrong uwtable
define dso_local i8* @thr1(i8* %0) #0 !dbg !39 {
  call void @llvm.dbg.value(metadata i8* undef, metadata !44, metadata !DIExpression()), !dbg !47
  store i32 1, i32* @flag1, align 4, !dbg !48, !tbaa !49
  br label %2, !dbg !53

2:                                                ; preds = %11, %1
  %3 = load i32, i32* @flag2, align 4, !dbg !54, !tbaa !49
  %4 = icmp sgt i32 %3, 0, !dbg !55
  br i1 %4, label %5, label %12, !dbg !53

5:                                                ; preds = %2
  %6 = load i32, i32* @turn, align 4, !dbg !56, !tbaa !49
  %.not = icmp eq i32 %6, 0, !dbg !59
  br i1 %.not, label %11, label %7, !dbg !60

7:                                                ; preds = %5
  store i32 0, i32* @flag1, align 4, !dbg !61, !tbaa !49
  br label %8, !dbg !63

8:                                                ; preds = %8, %7
  %9 = load i32, i32* @turn, align 4, !dbg !64, !tbaa !49
  %.not1 = icmp eq i32 %9, 0, !dbg !65
  br i1 %.not1, label %10, label %8, !dbg !63, !llvm.loop !66

10:                                               ; preds = %8
  store i32 1, i32* @flag1, align 4, !dbg !69, !tbaa !49
  br label %11, !dbg !70

11:                                               ; preds = %5, %10
  br label %2, !dbg !53, !llvm.loop !71

12:                                               ; preds = %2
  store volatile i32 0, i32* @x, align 4, !dbg !73, !tbaa !49
  %13 = load volatile i32, i32* @x, align 4, !dbg !74, !tbaa !49
  %14 = icmp slt i32 %13, 1, !dbg !74
  br i1 %14, label %16, label %15, !dbg !75

15:                                               ; preds = %12
  call void @llvm.dbg.label(metadata !45), !dbg !74
  call void @reach_error(), !dbg !74
  br label %16, !dbg !74

16:                                               ; preds = %15, %12
  store i32 1, i32* @turn, align 4, !dbg !76, !tbaa !49
  store i32 0, i32* @flag1, align 4, !dbg !77, !tbaa !49
  ret i8* null, !dbg !78
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.label(metadata) #1

; Function Attrs: nounwind sspstrong uwtable
define dso_local i8* @thr2(i8* %0) #0 !dbg !79 {
  call void @llvm.dbg.value(metadata i8* undef, metadata !81, metadata !DIExpression()), !dbg !84
  store i32 1, i32* @flag2, align 4, !dbg !85, !tbaa !49
  br label %2, !dbg !86

2:                                                ; preds = %11, %1
  %3 = load i32, i32* @flag1, align 4, !dbg !87, !tbaa !49
  %4 = icmp sgt i32 %3, 0, !dbg !88
  br i1 %4, label %5, label %12, !dbg !86

5:                                                ; preds = %2
  %6 = load i32, i32* @turn, align 4, !dbg !89, !tbaa !49
  %.not = icmp eq i32 %6, 1, !dbg !92
  br i1 %.not, label %11, label %7, !dbg !93

7:                                                ; preds = %5
  store i32 0, i32* @flag2, align 4, !dbg !94, !tbaa !49
  br label %8, !dbg !96

8:                                                ; preds = %8, %7
  %9 = load i32, i32* @turn, align 4, !dbg !97, !tbaa !49
  %.not1 = icmp eq i32 %9, 1, !dbg !98
  br i1 %.not1, label %10, label %8, !dbg !96, !llvm.loop !99

10:                                               ; preds = %8
  store i32 1, i32* @flag2, align 4, !dbg !101, !tbaa !49
  br label %11, !dbg !102

11:                                               ; preds = %5, %10
  br label %2, !dbg !86, !llvm.loop !103

12:                                               ; preds = %2
  store volatile i32 1, i32* @x, align 4, !dbg !105, !tbaa !49
  %13 = load volatile i32, i32* @x, align 4, !dbg !106, !tbaa !49
  %14 = icmp sgt i32 %13, 0, !dbg !106
  br i1 %14, label %16, label %15, !dbg !107

15:                                               ; preds = %12
  call void @llvm.dbg.label(metadata !82), !dbg !106
  call void @reach_error(), !dbg !106
  br label %16, !dbg !106

16:                                               ; preds = %15, %12
  store i32 1, i32* @turn, align 4, !dbg !108, !tbaa !49
  store i32 0, i32* @flag2, align 4, !dbg !109, !tbaa !49
  ret i8* null, !dbg !110
}

; Function Attrs: nounwind sspstrong uwtable
define dso_local i32 @main() #0 !dbg !111 {
  %1 = alloca i64, align 8
  %2 = alloca i64, align 8
  %3 = bitcast i64* %1 to i8*, !dbg !120
  call void @llvm.lifetime.start.p0i8(i64 8, i8* nonnull %3) #8, !dbg !120
  %4 = bitcast i64* %2 to i8*, !dbg !120
  call void @llvm.lifetime.start.p0i8(i64 8, i8* nonnull %4) #8, !dbg !120
  %5 = load i32, i32* @turn, align 4, !dbg !121, !tbaa !49
  %6 = icmp sgt i32 %5, -1, !dbg !122
  %7 = load i32, i32* @turn, align 4, !dbg !123
  %8 = icmp slt i32 %7, 2, !dbg !123
  %phi.cast = zext i1 %8 to i32, !dbg !123
  %9 = select i1 %6, i32 %phi.cast, i32 0, !dbg !123
  call void @assume_abort_if_not(i32 %9), !dbg !124
  call void @llvm.dbg.value(metadata i64* %1, metadata !115, metadata !DIExpression(DW_OP_deref)), !dbg !125
  %10 = call i32 @pthread_create(i64* nonnull %1, %union.pthread_attr_t* null, i8* (i8*)* nonnull @thr1, i8* null) #8, !dbg !126
  call void @llvm.dbg.value(metadata i64* %2, metadata !119, metadata !DIExpression(DW_OP_deref)), !dbg !125
  %11 = call i32 @pthread_create(i64* nonnull %2, %union.pthread_attr_t* null, i8* (i8*)* nonnull @thr2, i8* null) #8, !dbg !127
  %12 = load i64, i64* %1, align 8, !dbg !128, !tbaa !129
  call void @llvm.dbg.value(metadata i64 %12, metadata !115, metadata !DIExpression()), !dbg !125
  %13 = call i32 @pthread_join(i64 %12, i8** null) #8, !dbg !131
  %14 = load i64, i64* %2, align 8, !dbg !132, !tbaa !129
  call void @llvm.dbg.value(metadata i64 %14, metadata !119, metadata !DIExpression()), !dbg !125
  %15 = call i32 @pthread_join(i64 %14, i8** null) #8, !dbg !133
  %16 = bitcast i64* %2 to i8*, !dbg !134
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %16) #8, !dbg !134
  %17 = bitcast i64* %1 to i8*, !dbg !134
  call void @llvm.lifetime.end.p0i8(i64 8, i8* nonnull %17) #8, !dbg !134
  ret i32 0, !dbg !135
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #4

; Function Attrs: nounwind
declare !dbg !136 i32 @pthread_create(i64*, %union.pthread_attr_t*, i8* (i8*)*, i8*) #5

declare !dbg !153 i32 @pthread_join(i64, i8**) #6

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #4

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.value(metadata, metadata, metadata) #1

attributes #0 = { nounwind sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }
attributes #2 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { argmemonly nounwind willreturn }
attributes #5 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #7 = { noreturn nounwind }
attributes #8 = { nounwind }

!llvm.dbg.cu = !{!2}
!llvm.module.flags = !{!15, !16, !17, !18, !19}
!llvm.ident = !{!20}

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
!13 = distinct !DIGlobalVariable(name: "x", scope: !2, file: !8, line: 18, type: !14, isLocal: false, isDefinition: true)
!14 = !DIDerivedType(tag: DW_TAG_volatile_type, baseType: !9)
!15 = !{i32 7, !"Dwarf Version", i32 4}
!16 = !{i32 2, !"Debug Info Version", i32 3}
!17 = !{i32 1, !"wchar_size", i32 4}
!18 = !{i32 7, !"PIC Level", i32 2}
!19 = !{i32 7, !"PIE Level", i32 2}
!20 = !{!"clang version 11.1.0"}
!21 = distinct !DISubprogram(name: "assume_abort_if_not", scope: !8, file: !8, line: 2, type: !22, scopeLine: 2, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !24)
!22 = !DISubroutineType(types: !23)
!23 = !{null, !9}
!24 = !{!25}
!25 = !DILocalVariable(name: "cond", arg: 1, scope: !21, file: !8, line: 2, type: !9)
!26 = !DILocation(line: 0, scope: !21)
!27 = !DILocation(line: 3, column: 7, scope: !28)
!28 = distinct !DILexicalBlock(scope: !21, file: !8, line: 3, column: 6)
!29 = !DILocation(line: 3, column: 6, scope: !21)
!30 = !DILocation(line: 3, column: 14, scope: !31)
!31 = distinct !DILexicalBlock(scope: !28, file: !8, line: 3, column: 13)
!32 = !DILocation(line: 4, column: 1, scope: !21)
!33 = distinct !DISubprogram(name: "reach_error", scope: !8, file: !8, line: 7, type: !34, scopeLine: 7, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !4)
!34 = !DISubroutineType(types: !35)
!35 = !{null}
!36 = !DILocation(line: 7, column: 22, scope: !37)
!37 = distinct !DILexicalBlock(scope: !38, file: !8, line: 7, column: 22)
!38 = distinct !DILexicalBlock(scope: !33, file: !8, line: 7, column: 22)
!39 = distinct !DISubprogram(name: "thr1", scope: !8, file: !8, line: 20, type: !40, scopeLine: 20, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !43)
!40 = !DISubroutineType(types: !41)
!41 = !{!42, !42}
!42 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!43 = !{!44, !45}
!44 = !DILocalVariable(name: "_", arg: 1, scope: !39, file: !8, line: 20, type: !42)
!45 = !DILabel(scope: !46, name: "ERROR", file: !8, line: 31)
!46 = distinct !DILexicalBlock(scope: !39, file: !8, line: 31, column: 3)
!47 = !DILocation(line: 0, scope: !39)
!48 = !DILocation(line: 21, column: 9, scope: !39)
!49 = !{!50, !50, i64 0}
!50 = !{!"int", !51, i64 0}
!51 = !{!"omnipotent char", !52, i64 0}
!52 = !{!"Simple C/C++ TBAA"}
!53 = !DILocation(line: 22, column: 3, scope: !39)
!54 = !DILocation(line: 22, column: 10, scope: !39)
!55 = !DILocation(line: 22, column: 16, scope: !39)
!56 = !DILocation(line: 23, column: 9, scope: !57)
!57 = distinct !DILexicalBlock(scope: !58, file: !8, line: 23, column: 9)
!58 = distinct !DILexicalBlock(scope: !39, file: !8, line: 22, column: 22)
!59 = !DILocation(line: 23, column: 14, scope: !57)
!60 = !DILocation(line: 23, column: 9, scope: !58)
!61 = !DILocation(line: 24, column: 13, scope: !62)
!62 = distinct !DILexicalBlock(scope: !57, file: !8, line: 23, column: 20)
!63 = !DILocation(line: 25, column: 7, scope: !62)
!64 = !DILocation(line: 25, column: 14, scope: !62)
!65 = !DILocation(line: 25, column: 19, scope: !62)
!66 = distinct !{!66, !63, !67, !68}
!67 = !DILocation(line: 25, column: 26, scope: !62)
!68 = !{!"llvm.loop.unroll.disable"}
!69 = !DILocation(line: 26, column: 13, scope: !62)
!70 = !DILocation(line: 27, column: 5, scope: !62)
!71 = distinct !{!71, !53, !72, !68}
!72 = !DILocation(line: 28, column: 3, scope: !39)
!73 = !DILocation(line: 30, column: 5, scope: !39)
!74 = !DILocation(line: 31, column: 3, scope: !46)
!75 = !DILocation(line: 31, column: 3, scope: !39)
!76 = !DILocation(line: 33, column: 8, scope: !39)
!77 = !DILocation(line: 34, column: 9, scope: !39)
!78 = !DILocation(line: 35, column: 3, scope: !39)
!79 = distinct !DISubprogram(name: "thr2", scope: !8, file: !8, line: 38, type: !40, scopeLine: 38, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !80)
!80 = !{!81, !82}
!81 = !DILocalVariable(name: "_", arg: 1, scope: !79, file: !8, line: 38, type: !42)
!82 = !DILabel(scope: !83, name: "ERROR", file: !8, line: 49)
!83 = distinct !DILexicalBlock(scope: !79, file: !8, line: 49, column: 3)
!84 = !DILocation(line: 0, scope: !79)
!85 = !DILocation(line: 39, column: 9, scope: !79)
!86 = !DILocation(line: 40, column: 3, scope: !79)
!87 = !DILocation(line: 40, column: 10, scope: !79)
!88 = !DILocation(line: 40, column: 16, scope: !79)
!89 = !DILocation(line: 41, column: 9, scope: !90)
!90 = distinct !DILexicalBlock(scope: !91, file: !8, line: 41, column: 9)
!91 = distinct !DILexicalBlock(scope: !79, file: !8, line: 40, column: 22)
!92 = !DILocation(line: 41, column: 14, scope: !90)
!93 = !DILocation(line: 41, column: 9, scope: !91)
!94 = !DILocation(line: 42, column: 13, scope: !95)
!95 = distinct !DILexicalBlock(scope: !90, file: !8, line: 41, column: 20)
!96 = !DILocation(line: 43, column: 7, scope: !95)
!97 = !DILocation(line: 43, column: 14, scope: !95)
!98 = !DILocation(line: 43, column: 19, scope: !95)
!99 = distinct !{!99, !96, !100, !68}
!100 = !DILocation(line: 43, column: 26, scope: !95)
!101 = !DILocation(line: 44, column: 13, scope: !95)
!102 = !DILocation(line: 45, column: 5, scope: !95)
!103 = distinct !{!103, !86, !104, !68}
!104 = !DILocation(line: 46, column: 3, scope: !79)
!105 = !DILocation(line: 48, column: 5, scope: !79)
!106 = !DILocation(line: 49, column: 3, scope: !83)
!107 = !DILocation(line: 49, column: 3, scope: !79)
!108 = !DILocation(line: 51, column: 8, scope: !79)
!109 = !DILocation(line: 52, column: 9, scope: !79)
!110 = !DILocation(line: 53, column: 3, scope: !79)
!111 = distinct !DISubprogram(name: "main", scope: !8, file: !8, line: 56, type: !112, scopeLine: 56, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !114)
!112 = !DISubroutineType(types: !113)
!113 = !{!9}
!114 = !{!115, !119}
!115 = !DILocalVariable(name: "t1", scope: !111, file: !8, line: 57, type: !116)
!116 = !DIDerivedType(tag: DW_TAG_typedef, name: "pthread_t", file: !117, line: 27, baseType: !118)
!117 = !DIFile(filename: "/usr/include/bits/pthreadtypes.h", directory: "")
!118 = !DIBasicType(name: "long unsigned int", size: 64, encoding: DW_ATE_unsigned)
!119 = !DILocalVariable(name: "t2", scope: !111, file: !8, line: 57, type: !116)
!120 = !DILocation(line: 57, column: 3, scope: !111)
!121 = !DILocation(line: 58, column: 26, scope: !111)
!122 = !DILocation(line: 58, column: 24, scope: !111)
!123 = !DILocation(line: 58, column: 31, scope: !111)
!124 = !DILocation(line: 58, column: 3, scope: !111)
!125 = !DILocation(line: 0, scope: !111)
!126 = !DILocation(line: 59, column: 3, scope: !111)
!127 = !DILocation(line: 60, column: 3, scope: !111)
!128 = !DILocation(line: 61, column: 16, scope: !111)
!129 = !{!130, !130, i64 0}
!130 = !{!"long", !51, i64 0}
!131 = !DILocation(line: 61, column: 3, scope: !111)
!132 = !DILocation(line: 62, column: 16, scope: !111)
!133 = !DILocation(line: 62, column: 3, scope: !111)
!134 = !DILocation(line: 64, column: 1, scope: !111)
!135 = !DILocation(line: 63, column: 3, scope: !111)
!136 = !DISubprogram(name: "pthread_create", scope: !137, file: !137, line: 200, type: !138, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !4)
!137 = !DIFile(filename: "/usr/include/pthread.h", directory: "")
!138 = !DISubroutineType(types: !139)
!139 = !{!9, !140, !141, !152, !42}
!140 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !118, size: 64)
!141 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !142, size: 64)
!142 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !143)
!143 = distinct !DICompositeType(tag: DW_TAG_union_type, name: "pthread_attr_t", file: !117, line: 56, size: 448, elements: !144)
!144 = !{!145, !150}
!145 = !DIDerivedType(tag: DW_TAG_member, name: "__size", scope: !143, file: !117, line: 58, baseType: !146, size: 448)
!146 = !DICompositeType(tag: DW_TAG_array_type, baseType: !147, size: 448, elements: !148)
!147 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!148 = !{!149}
!149 = !DISubrange(count: 56)
!150 = !DIDerivedType(tag: DW_TAG_member, name: "__align", scope: !143, file: !117, line: 59, baseType: !151, size: 64)
!151 = !DIBasicType(name: "long int", size: 64, encoding: DW_ATE_signed)
!152 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !40, size: 64)
!153 = !DISubprogram(name: "pthread_join", scope: !137, file: !137, line: 217, type: !154, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !4)
!154 = !DISubroutineType(types: !155)
!155 = !{!9, !118, !156}
!156 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !42, size: 64)
