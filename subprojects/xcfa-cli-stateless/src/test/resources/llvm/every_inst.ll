; ModuleID = 'every_inst.bc'
source_filename = "every_inst.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [3 x i8] c"%d\00", align 1
@.str.1 = private unnamed_addr constant [4 x i8] c"if\0A\00", align 1
@.str.2 = private unnamed_addr constant [6 x i8] c"else\0A\00", align 1
@.str.3 = private unnamed_addr constant [3 x i8] c"0\0A\00", align 1
@.str.4 = private unnamed_addr constant [3 x i8] c"1\0A\00", align 1
@.str.5 = private unnamed_addr constant [3 x i8] c"2\0A\00", align 1
@.str.6 = private unnamed_addr constant [7 x i8] c"other\0A\00", align 1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @ifoo(i32 %0, i32* %1) #0 !dbg !9 {
  %3 = alloca i32, align 4
  %4 = alloca i32*, align 8
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !14, metadata !DIExpression()), !dbg !15
  store i32* %1, i32** %4, align 8
  call void @llvm.dbg.declare(metadata i32** %4, metadata !16, metadata !DIExpression()), !dbg !17
  %5 = load i32, i32* %3, align 4, !dbg !18
  %6 = load i32*, i32** %4, align 8, !dbg !19
  store i32 %5, i32* %6, align 4, !dbg !20
  ret i32 -1, !dbg !21
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @foo() #0 !dbg !22 {
  ret void, !dbg !25
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @main() #0 !dbg !26 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !29, metadata !DIExpression()), !dbg !30
  %9 = call i32 (i8*, ...) @__isoc99_scanf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str, i64 0, i64 0), i32* %2), !dbg !31
  %10 = load i32, i32* %2, align 4, !dbg !32
  %11 = icmp ne i32 %10, 0, !dbg !32
  br i1 %11, label %12, label %14, !dbg !34

12:                                               ; preds = %0
  %13 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1, i64 0, i64 0)), !dbg !35
  br label %16, !dbg !37

14:                                               ; preds = %0
  %15 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @.str.2, i64 0, i64 0)), !dbg !38
  br label %16

16:                                               ; preds = %14, %12
  %17 = load i32, i32* %2, align 4, !dbg !40
  switch i32 %17, label %24 [
    i32 0, label %18
    i32 1, label %20
    i32 2, label %22
  ], !dbg !41

18:                                               ; preds = %16
  %19 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.3, i64 0, i64 0)), !dbg !42
  br label %26, !dbg !44

20:                                               ; preds = %16
  %21 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4, i64 0, i64 0)), !dbg !45
  br label %26, !dbg !46

22:                                               ; preds = %16
  %23 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.5, i64 0, i64 0)), !dbg !47
  br label %26, !dbg !48

24:                                               ; preds = %16
  %25 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.6, i64 0, i64 0)), !dbg !49
  br label %26, !dbg !50

26:                                               ; preds = %24, %22, %20, %18
  call void @llvm.dbg.declare(metadata i32* %3, metadata !51, metadata !DIExpression()), !dbg !52
  %27 = load i32, i32* %2, align 4, !dbg !53
  %28 = add nsw i32 %27, 2, !dbg !54
  store i32 %28, i32* %3, align 4, !dbg !52
  call void @llvm.dbg.declare(metadata i32* %4, metadata !55, metadata !DIExpression()), !dbg !56
  %29 = load i32, i32* %3, align 4, !dbg !57
  %30 = sub nsw i32 %29, 3, !dbg !58
  store i32 %30, i32* %4, align 4, !dbg !56
  call void @llvm.dbg.declare(metadata i32* %5, metadata !59, metadata !DIExpression()), !dbg !60
  %31 = load i32, i32* %4, align 4, !dbg !61
  %32 = load i32, i32* %4, align 4, !dbg !62
  %33 = mul nsw i32 %31, %32, !dbg !63
  store i32 %33, i32* %5, align 4, !dbg !60
  call void @llvm.dbg.declare(metadata i32* %6, metadata !64, metadata !DIExpression()), !dbg !65
  %34 = load i32, i32* %5, align 4, !dbg !66
  %35 = load i32, i32* %4, align 4, !dbg !67
  %36 = sdiv i32 %34, %35, !dbg !68
  store i32 %36, i32* %6, align 4, !dbg !65
  call void @llvm.dbg.declare(metadata i32* %7, metadata !69, metadata !DIExpression()), !dbg !70
  %37 = load i32, i32* %5, align 4, !dbg !71
  %38 = srem i32 %37, 2, !dbg !72
  store i32 %38, i32* %7, align 4, !dbg !70
  call void @llvm.dbg.declare(metadata i32* %8, metadata !73, metadata !DIExpression()), !dbg !74
  %39 = load i32, i32* %2, align 4, !dbg !75
  %40 = icmp ne i32 %39, 0, !dbg !75
  br i1 %40, label %44, label %41, !dbg !76

41:                                               ; preds = %26
  %42 = load i32, i32* %3, align 4, !dbg !77
  %43 = icmp ne i32 %42, 0, !dbg !76
  br label %44, !dbg !76

44:                                               ; preds = %41, %26
  %45 = phi i1 [ true, %26 ], [ %43, %41 ]
  %46 = zext i1 %45 to i32, !dbg !76
  store i32 %46, i32* %8, align 4, !dbg !74
  call void @foo(), !dbg !78
  %47 = load i32, i32* %2, align 4, !dbg !79
  %48 = call i32 @ifoo(i32 %47, i32* %3), !dbg !80
  ret i32 %48, !dbg !81
}

declare i32 @__isoc99_scanf(i8*, ...) #2

declare i32 @printf(i8*, ...) #2

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6, !7}
!llvm.ident = !{!8}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 11.1.0", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "every_inst.c", directory: "/home/levente/Documents/University/theta/subprojects/xcfa-cli-stateless/src/test/resources/llvm")
!2 = !{}
!3 = !{i32 7, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{i32 7, !"PIE Level", i32 2}
!8 = !{!"clang version 11.1.0"}
!9 = distinct !DISubprogram(name: "ifoo", scope: !1, file: !1, line: 1, type: !10, scopeLine: 1, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!10 = !DISubroutineType(types: !11)
!11 = !{!12, !12, !13}
!12 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!13 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !12, size: 64)
!14 = !DILocalVariable(name: "a", arg: 1, scope: !9, file: !1, line: 1, type: !12)
!15 = !DILocation(line: 1, column: 14, scope: !9)
!16 = !DILocalVariable(name: "b", arg: 2, scope: !9, file: !1, line: 1, type: !13)
!17 = !DILocation(line: 1, column: 21, scope: !9)
!18 = !DILocation(line: 2, column: 10, scope: !9)
!19 = !DILocation(line: 2, column: 6, scope: !9)
!20 = !DILocation(line: 2, column: 8, scope: !9)
!21 = !DILocation(line: 3, column: 5, scope: !9)
!22 = distinct !DISubprogram(name: "foo", scope: !1, file: !1, line: 6, type: !23, scopeLine: 6, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!23 = !DISubroutineType(types: !24)
!24 = !{null}
!25 = !DILocation(line: 7, column: 1, scope: !22)
!26 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 11, type: !27, scopeLine: 11, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!27 = !DISubroutineType(types: !28)
!28 = !{!12}
!29 = !DILocalVariable(name: "a", scope: !26, file: !1, line: 12, type: !12)
!30 = !DILocation(line: 12, column: 9, scope: !26)
!31 = !DILocation(line: 13, column: 5, scope: !26)
!32 = !DILocation(line: 14, column: 8, scope: !33)
!33 = distinct !DILexicalBlock(scope: !26, file: !1, line: 14, column: 8)
!34 = !DILocation(line: 14, column: 8, scope: !26)
!35 = !DILocation(line: 15, column: 9, scope: !36)
!36 = distinct !DILexicalBlock(scope: !33, file: !1, line: 14, column: 11)
!37 = !DILocation(line: 16, column: 5, scope: !36)
!38 = !DILocation(line: 18, column: 9, scope: !39)
!39 = distinct !DILexicalBlock(scope: !33, file: !1, line: 17, column: 10)
!40 = !DILocation(line: 21, column: 12, scope: !26)
!41 = !DILocation(line: 21, column: 5, scope: !26)
!42 = !DILocation(line: 22, column: 17, scope: !43)
!43 = distinct !DILexicalBlock(scope: !26, file: !1, line: 21, column: 15)
!44 = !DILocation(line: 22, column: 32, scope: !43)
!45 = !DILocation(line: 23, column: 17, scope: !43)
!46 = !DILocation(line: 23, column: 32, scope: !43)
!47 = !DILocation(line: 24, column: 17, scope: !43)
!48 = !DILocation(line: 24, column: 32, scope: !43)
!49 = !DILocation(line: 25, column: 18, scope: !43)
!50 = !DILocation(line: 25, column: 37, scope: !43)
!51 = !DILocalVariable(name: "b", scope: !26, file: !1, line: 28, type: !12)
!52 = !DILocation(line: 28, column: 9, scope: !26)
!53 = !DILocation(line: 28, column: 13, scope: !26)
!54 = !DILocation(line: 28, column: 15, scope: !26)
!55 = !DILocalVariable(name: "c", scope: !26, file: !1, line: 29, type: !12)
!56 = !DILocation(line: 29, column: 9, scope: !26)
!57 = !DILocation(line: 29, column: 13, scope: !26)
!58 = !DILocation(line: 29, column: 15, scope: !26)
!59 = !DILocalVariable(name: "d", scope: !26, file: !1, line: 30, type: !12)
!60 = !DILocation(line: 30, column: 9, scope: !26)
!61 = !DILocation(line: 30, column: 13, scope: !26)
!62 = !DILocation(line: 30, column: 15, scope: !26)
!63 = !DILocation(line: 30, column: 14, scope: !26)
!64 = !DILocalVariable(name: "e", scope: !26, file: !1, line: 31, type: !12)
!65 = !DILocation(line: 31, column: 9, scope: !26)
!66 = !DILocation(line: 31, column: 13, scope: !26)
!67 = !DILocation(line: 31, column: 15, scope: !26)
!68 = !DILocation(line: 31, column: 14, scope: !26)
!69 = !DILocalVariable(name: "f", scope: !26, file: !1, line: 32, type: !12)
!70 = !DILocation(line: 32, column: 9, scope: !26)
!71 = !DILocation(line: 32, column: 13, scope: !26)
!72 = !DILocation(line: 32, column: 15, scope: !26)
!73 = !DILocalVariable(name: "i", scope: !26, file: !1, line: 34, type: !12)
!74 = !DILocation(line: 34, column: 9, scope: !26)
!75 = !DILocation(line: 34, column: 13, scope: !26)
!76 = !DILocation(line: 34, column: 15, scope: !26)
!77 = !DILocation(line: 34, column: 18, scope: !26)
!78 = !DILocation(line: 36, column: 5, scope: !26)
!79 = !DILocation(line: 37, column: 17, scope: !26)
!80 = !DILocation(line: 37, column: 12, scope: !26)
!81 = !DILocation(line: 37, column: 5, scope: !26)
