; ModuleID = '/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/array_standard_compare_ground.bc'
source_filename = "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/array_standard_compare_ground.i"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1
@.str.1 = private unnamed_addr constant [26 x i8] c"standard_compare_ground.c\00", align 1
@__PRETTY_FUNCTION__.reach_error = private unnamed_addr constant [19 x i8] c"void reach_error()\00", align 1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(i8*, i8*, i32, i8*) local_unnamed_addr #0

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.label(metadata) #1

; Function Attrs: nounwind sspstrong uwtable
define dso_local i32 @main() local_unnamed_addr #2 !dbg !9 {
  %1 = alloca [100000 x i32], align 16
  %2 = alloca [100000 x i32], align 16
  %3 = bitcast [100000 x i32]* %1 to i8*, !dbg !27
  call void @llvm.lifetime.start.p0i8(i64 400000, i8* nonnull %3) #5, !dbg !27
  call void @llvm.dbg.declare(metadata [100000 x i32]* %1, metadata !15, metadata !DIExpression()), !dbg !28
  %4 = bitcast [100000 x i32]* %2 to i8*, !dbg !29
  call void @llvm.lifetime.start.p0i8(i64 400000, i8* nonnull %4) #5, !dbg !29
  call void @llvm.dbg.declare(metadata [100000 x i32]* %2, metadata !19, metadata !DIExpression()), !dbg !30
  call void @llvm.dbg.value(metadata i32 0, metadata !20, metadata !DIExpression()), !dbg !31
  br label %5, !dbg !32

5:                                                ; preds = %Flow5, %0
  %.02 = phi i32 [ 0, %0 ], [ %12, %Flow5 ], !dbg !31
  call void @llvm.dbg.value(metadata i32 %.02, metadata !20, metadata !DIExpression()), !dbg !31
  %6 = icmp ult i32 %.02, 100000, !dbg !33
  %undefv = call i32 @gazer.undef_value.i32()
  br i1 %6, label %7, label %Flow5

7:                                                ; preds = %5
  %8 = call i32 (...) @__VERIFIER_nondet_int() #5, !dbg !35
  %9 = zext i32 %.02 to i64, !dbg !37
  call void @setArrayElement([100000 x i32]* %1, i64 %9, i32 %8), !dbg !38
  %10 = call i32 (...) @__VERIFIER_nondet_int() #5, !dbg !39
  call void @setArrayElement([100000 x i32]* %2, i64 %9, i32 %10), !dbg !40
  %11 = add nuw nsw i32 %.02, 1, !dbg !41
  call void @llvm.dbg.value(metadata i32 %11, metadata !20, metadata !DIExpression()), !dbg !31
  br label %Flow5

Flow5:                                            ; preds = %7, %5
  %12 = phi i32 [ %11, %7 ], [ %undefv, %5 ]
  %13 = phi i1 [ false, %7 ], [ true, %5 ]
  br i1 %13, label %.preheader6, label %5

.preheader6:                                      ; preds = %Flow5, %Flow
  %.03 = phi i32 [ %21, %Flow ], [ 0, %Flow5 ], !dbg !42
  %.01 = phi i32 [ %20, %Flow ], [ 1, %Flow5 ], !dbg !42
  call void @llvm.dbg.value(metadata i32 %.01, metadata !23, metadata !DIExpression()), !dbg !42
  call void @llvm.dbg.value(metadata i32 %.03, metadata !22, metadata !DIExpression()), !dbg !42
  %14 = icmp ult i32 %.03, 100000, !dbg !43
  %undefv8 = call i32 @gazer.undef_value.i32()
  %undefv9 = call i32 @gazer.undef_value.i32()
  br i1 %14, label %15, label %Flow

15:                                               ; preds = %.preheader6
  %16 = zext i32 %.03 to i64, !dbg !44
  %17 = call i32 @getArrayElement_i32([100000 x i32]* %1, i64 %16), !dbg !44
  %18 = call i32 @getArrayElement_i32([100000 x i32]* %2, i64 %16), !dbg !47
  %.not4 = icmp eq i32 %17, %18, !dbg !48
  %spec.select = select i1 %.not4, i32 %.01, i32 0, !dbg !49
  call void @llvm.dbg.value(metadata i32 %spec.select, metadata !23, metadata !DIExpression()), !dbg !42
  %19 = add nuw nsw i32 %.03, 1, !dbg !50
  call void @llvm.dbg.value(metadata i32 %19, metadata !22, metadata !DIExpression()), !dbg !42
  br label %Flow

Flow:                                             ; preds = %15, %.preheader6
  %20 = phi i32 [ %spec.select, %15 ], [ %undefv8, %.preheader6 ]
  %21 = phi i32 [ %19, %15 ], [ %undefv9, %.preheader6 ]
  %22 = phi i1 [ false, %15 ], [ true, %.preheader6 ]
  br i1 %22, label %23, label %.preheader6

23:                                               ; preds = %Flow
  call void @llvm.dbg.value(metadata i32 undef, metadata !23, metadata !DIExpression()), !dbg !42
  %.not = icmp eq i32 %.01, 0, !dbg !51
  br i1 %.not, label %.loopexit, label %__VERIFIER_assert.exit, !dbg !52

__VERIFIER_assert.exit:                           ; preds = %23, %27
  %indvars.iv = phi i64 [ %indvars.iv.next, %27 ], [ 0, %23 ]
  call void @llvm.dbg.value(metadata i64 %indvars.iv, metadata !24, metadata !DIExpression()), !dbg !53
  %24 = call i32 @getArrayElement_i32([100000 x i32]* %1, i64 %indvars.iv), !dbg !54
  %25 = call i32 @getArrayElement_i32([100000 x i32]* %2, i64 %indvars.iv), !dbg !58
  %26 = icmp eq i32 %24, %25, !dbg !59
  call void @llvm.dbg.value(metadata i1 %26, metadata !60, metadata !DIExpression(DW_OP_LLVM_convert, 1, DW_ATE_unsigned, DW_OP_LLVM_convert, 32, DW_ATE_unsigned, DW_OP_stack_value)), !dbg !68
  call void @llvm.dbg.value(metadata i64 %indvars.iv, metadata !24, metadata !DIExpression(DW_OP_plus_uconst, 1, DW_OP_stack_value)), !dbg !53
  br i1 %26, label %27, label %28, !dbg !70

27:                                               ; preds = %__VERIFIER_assert.exit
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1, !dbg !71
  call void @llvm.dbg.value(metadata i64 %indvars.iv, metadata !24, metadata !DIExpression(DW_OP_plus_uconst, 1, DW_OP_stack_value)), !dbg !53
  %exitcond.not = icmp eq i64 %indvars.iv.next, 100000, !dbg !72
  br i1 %exitcond.not, label %.loopexit, label %__VERIFIER_assert.exit, !dbg !73, !llvm.loop !74

28:                                               ; preds = %__VERIFIER_assert.exit
  call void @llvm.dbg.label(metadata !65) #5, !dbg !77
  call void @__assert_fail(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([26 x i8], [26 x i8]* @.str.1, i64 0, i64 0), i32 3, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @__PRETTY_FUNCTION__.reach_error, i64 0, i64 0)) #6, !dbg !78
  unreachable, !dbg !78

.loopexit:                                        ; preds = %27, %23
  call void @llvm.lifetime.end.p0i8(i64 400000, i8* nonnull %4) #5, !dbg !86
  call void @llvm.lifetime.end.p0i8(i64 400000, i8* nonnull %3) #5, !dbg !86
  ret i32 0, !dbg !87
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #3

declare i32 @__VERIFIER_nondet_int(...) local_unnamed_addr #4

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #3

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.value(metadata, metadata, metadata) #1

declare i32 @gazer.undef_value.i32()

declare void @setArrayElement(void, void, void)

declare i32 @getArrayElement_i32(void, void)

attributes #0 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }
attributes #2 = { nounwind sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nounwind willreturn }
attributes #4 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nounwind }
attributes #6 = { noreturn nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6, !7}
!llvm.ident = !{!8}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 11.1.0", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/array_standard_compare_ground.i", directory: "/home/levente/Documents/University/theta")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{i32 7, !"PIE Level", i32 2}
!8 = !{!"clang version 11.1.0"}
!9 = distinct !DISubprogram(name: "main", scope: !10, file: !10, line: 16, type: !11, scopeLine: 16, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !14)
!10 = !DIFile(filename: "subprojects/xcfa-cli/src/test/resources/llvm/array_standard_compare_ground.i", directory: "/home/levente/Documents/University/theta")
!11 = !DISubroutineType(types: !12)
!12 = !{!13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{!15, !19, !20, !22, !23, !24}
!15 = !DILocalVariable(name: "a", scope: !9, file: !10, line: 17, type: !16)
!16 = !DICompositeType(tag: DW_TAG_array_type, baseType: !13, size: 3200000, elements: !17)
!17 = !{!18}
!18 = !DISubrange(count: 100000)
!19 = !DILocalVariable(name: "b", scope: !9, file: !10, line: 18, type: !16)
!20 = !DILocalVariable(name: "j", scope: !21, file: !10, line: 20, type: !13)
!21 = distinct !DILexicalBlock(scope: !9, file: !10, line: 20, column: 5)
!22 = !DILocalVariable(name: "i", scope: !9, file: !10, line: 25, type: !13)
!23 = !DILocalVariable(name: "rv", scope: !9, file: !10, line: 26, type: !13)
!24 = !DILocalVariable(name: "x", scope: !25, file: !10, line: 34, type: !13)
!25 = distinct !DILexicalBlock(scope: !26, file: !10, line: 33, column: 15)
!26 = distinct !DILexicalBlock(scope: !9, file: !10, line: 33, column: 10)
!27 = !DILocation(line: 17, column: 5, scope: !9)
!28 = !DILocation(line: 17, column: 9, scope: !9)
!29 = !DILocation(line: 18, column: 5, scope: !9)
!30 = !DILocation(line: 18, column: 9, scope: !9)
!31 = !DILocation(line: 0, scope: !21)
!32 = !DILocation(line: 20, column: 10, scope: !21)
!33 = !DILocation(line: 20, column: 23, scope: !34)
!34 = distinct !DILexicalBlock(scope: !21, file: !10, line: 20, column: 5)
!35 = !DILocation(line: 21, column: 16, scope: !36)
!36 = distinct !DILexicalBlock(scope: !34, file: !10, line: 20, column: 40)
!37 = !DILocation(line: 21, column: 9, scope: !36)
!38 = !DILocation(line: 21, column: 14, scope: !36)
!39 = !DILocation(line: 22, column: 16, scope: !36)
!40 = !DILocation(line: 22, column: 14, scope: !36)
!41 = !DILocation(line: 20, column: 35, scope: !34)
!42 = !DILocation(line: 0, scope: !9)
!43 = !DILocation(line: 27, column: 15, scope: !9)
!44 = !DILocation(line: 28, column: 14, scope: !45)
!45 = distinct !DILexicalBlock(scope: !46, file: !10, line: 28, column: 14)
!46 = distinct !DILexicalBlock(scope: !9, file: !10, line: 27, column: 26)
!47 = !DILocation(line: 28, column: 22, scope: !45)
!48 = !DILocation(line: 28, column: 19, scope: !45)
!49 = !DILocation(line: 28, column: 14, scope: !46)
!50 = !DILocation(line: 31, column: 14, scope: !46)
!51 = !DILocation(line: 33, column: 10, scope: !26)
!52 = !DILocation(line: 33, column: 10, scope: !9)
!53 = !DILocation(line: 0, scope: !25)
!54 = !DILocation(line: 36, column: 32, scope: !55)
!55 = distinct !DILexicalBlock(scope: !56, file: !10, line: 35, column: 42)
!56 = distinct !DILexicalBlock(scope: !57, file: !10, line: 35, column: 9)
!57 = distinct !DILexicalBlock(scope: !25, file: !10, line: 35, column: 9)
!58 = !DILocation(line: 36, column: 40, scope: !55)
!59 = !DILocation(line: 36, column: 37, scope: !55)
!60 = !DILocalVariable(name: "cond", arg: 1, scope: !61, file: !10, line: 13, type: !13)
!61 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !10, file: !10, line: 13, type: !62, scopeLine: 13, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !64)
!62 = !DISubroutineType(types: !63)
!63 = !{null, !13}
!64 = !{!60, !65}
!65 = !DILabel(scope: !66, name: "ERROR", file: !10, line: 13)
!66 = distinct !DILexicalBlock(scope: !67, file: !10, line: 13, column: 48)
!67 = distinct !DILexicalBlock(scope: !61, file: !10, line: 13, column: 39)
!68 = !DILocation(line: 0, scope: !61, inlinedAt: !69)
!69 = distinct !DILocation(line: 36, column: 13, scope: !55)
!70 = !DILocation(line: 13, column: 39, scope: !61, inlinedAt: !69)
!71 = !DILocation(line: 35, column: 37, scope: !56)
!72 = !DILocation(line: 35, column: 25, scope: !56)
!73 = !DILocation(line: 35, column: 9, scope: !57)
!74 = distinct !{!74, !73, !75, !76}
!75 = !DILocation(line: 37, column: 9, scope: !57)
!76 = !{!"llvm.loop.unroll.disable"}
!77 = !DILocation(line: 13, column: 50, scope: !66, inlinedAt: !69)
!78 = !DILocation(line: 12, column: 83, scope: !79, inlinedAt: !84)
!79 = distinct !DILexicalBlock(scope: !80, file: !10, line: 12, column: 73)
!80 = distinct !DILexicalBlock(scope: !81, file: !10, line: 12, column: 67)
!81 = distinct !DISubprogram(name: "reach_error", scope: !10, file: !10, line: 12, type: !82, scopeLine: 12, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !2)
!82 = !DISubroutineType(types: !83)
!83 = !{null}
!84 = distinct !DILocation(line: 13, column: 58, scope: !85, inlinedAt: !69)
!85 = distinct !DILexicalBlock(scope: !66, file: !10, line: 13, column: 57)
!86 = !DILocation(line: 40, column: 1, scope: !9)
!87 = !DILocation(line: 39, column: 5, scope: !9)
