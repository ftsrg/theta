; ModuleID = 'example_func_param.bc'
source_filename = "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/example_func_param.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [7 x i8] c"%d, %d\00", align 1

; Function Attrs: nounwind sspstrong uwtable
define dso_local i32 @adder(i32 %0, i32 %1) #0 !dbg !9 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 %0, i32* %3, align 4, !tbaa !19
  call void @llvm.dbg.declare(metadata i32* %3, metadata !15, metadata !DIExpression()), !dbg !23
  store i32 %1, i32* %4, align 4, !tbaa !19
  call void @llvm.dbg.declare(metadata i32* %4, metadata !16, metadata !DIExpression()), !dbg !24
  %7 = bitcast i32* %5 to i8*, !dbg !25
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %7) #4, !dbg !25
  call void @llvm.dbg.declare(metadata i32* %5, metadata !17, metadata !DIExpression()), !dbg !26
  %8 = load i32, i32* %3, align 4, !dbg !27, !tbaa !19
  store i32 %8, i32* %5, align 4, !dbg !26, !tbaa !19
  %9 = bitcast i32* %6 to i8*, !dbg !28
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %9) #4, !dbg !28
  call void @llvm.dbg.declare(metadata i32* %6, metadata !18, metadata !DIExpression()), !dbg !29
  %10 = load i32, i32* %4, align 4, !dbg !30, !tbaa !19
  store i32 %10, i32* %6, align 4, !dbg !29, !tbaa !19
  %11 = load i32, i32* %5, align 4, !dbg !31, !tbaa !19
  %12 = load i32, i32* %6, align 4, !dbg !32, !tbaa !19
  %13 = add nsw i32 %11, %12, !dbg !33
  %14 = bitcast i32* %6 to i8*, !dbg !34
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %14) #4, !dbg !34
  %15 = bitcast i32* %5 to i8*, !dbg !34
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %15) #4, !dbg !34
  ret i32 %13, !dbg !35
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #2

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #2

; Function Attrs: nounwind sspstrong uwtable
define dso_local i32 @main() #0 !dbg !36 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  %4 = bitcast i32* %2 to i8*, !dbg !42
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %4) #4, !dbg !42
  call void @llvm.dbg.declare(metadata i32* %2, metadata !40, metadata !DIExpression()), !dbg !43
  %5 = bitcast i32* %3 to i8*, !dbg !42
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %5) #4, !dbg !42
  call void @llvm.dbg.declare(metadata i32* %3, metadata !41, metadata !DIExpression()), !dbg !44
  %6 = call i32 (i8*, ...) @__isoc99_scanf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str, i64 0, i64 0), i32* %2, i32* %3), !dbg !45
  %7 = call i32 @adder(i32 2, i32 -2), !dbg !46
  %8 = bitcast i32* %3 to i8*, !dbg !47
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %8) #4, !dbg !47
  %9 = bitcast i32* %2 to i8*, !dbg !47
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %9) #4, !dbg !47
  ret i32 %7, !dbg !48
}

declare i32 @__isoc99_scanf(i8*, ...) #3

attributes #0 = { nounwind sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }
attributes #2 = { argmemonly nounwind willreturn }
attributes #3 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6, !7}
!llvm.ident = !{!8}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 11.1.0", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "/home/levente/Documents/University/theta/subprojects/xcfa-cli/src/test/resources/llvm/example_func_param.c", directory: "/home/levente/Documents/University/theta")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{i32 7, !"PIE Level", i32 2}
!8 = !{!"clang version 11.1.0"}
!9 = distinct !DISubprogram(name: "adder", scope: !10, file: !10, line: 1, type: !11, scopeLine: 1, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !14)
!10 = !DIFile(filename: "subprojects/xcfa-cli/src/test/resources/llvm/example_func_param.c", directory: "/home/levente/Documents/University/theta")
!11 = !DISubroutineType(types: !12)
!12 = !{!13, !13, !13}
!13 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!14 = !{!15, !16, !17, !18}
!15 = !DILocalVariable(name: "a", arg: 1, scope: !9, file: !10, line: 1, type: !13)
!16 = !DILocalVariable(name: "b", arg: 2, scope: !9, file: !10, line: 1, type: !13)
!17 = !DILocalVariable(name: "c", scope: !9, file: !10, line: 2, type: !13)
!18 = !DILocalVariable(name: "d", scope: !9, file: !10, line: 2, type: !13)
!19 = !{!20, !20, i64 0}
!20 = !{!"int", !21, i64 0}
!21 = !{!"omnipotent char", !22, i64 0}
!22 = !{!"Simple C/C++ TBAA"}
!23 = !DILocation(line: 1, column: 15, scope: !9)
!24 = !DILocation(line: 1, column: 22, scope: !9)
!25 = !DILocation(line: 2, column: 5, scope: !9)
!26 = !DILocation(line: 2, column: 9, scope: !9)
!27 = !DILocation(line: 2, column: 13, scope: !9)
!28 = !DILocation(line: 2, column: 16, scope: !9)
!29 = !DILocation(line: 2, column: 20, scope: !9)
!30 = !DILocation(line: 2, column: 24, scope: !9)
!31 = !DILocation(line: 3, column: 12, scope: !9)
!32 = !DILocation(line: 3, column: 14, scope: !9)
!33 = !DILocation(line: 3, column: 13, scope: !9)
!34 = !DILocation(line: 4, column: 1, scope: !9)
!35 = !DILocation(line: 3, column: 5, scope: !9)
!36 = distinct !DISubprogram(name: "main", scope: !10, file: !10, line: 6, type: !37, scopeLine: 6, flags: DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !0, retainedNodes: !39)
!37 = !DISubroutineType(types: !38)
!38 = !{!13}
!39 = !{!40, !41}
!40 = !DILocalVariable(name: "a", scope: !36, file: !10, line: 7, type: !13)
!41 = !DILocalVariable(name: "b", scope: !36, file: !10, line: 7, type: !13)
!42 = !DILocation(line: 7, column: 5, scope: !36)
!43 = !DILocation(line: 7, column: 9, scope: !36)
!44 = !DILocation(line: 7, column: 12, scope: !36)
!45 = !DILocation(line: 8, column: 5, scope: !36)
!46 = !DILocation(line: 9, column: 12, scope: !36)
!47 = !DILocation(line: 10, column: 1, scope: !36)
!48 = !DILocation(line: 9, column: 5, scope: !36)
