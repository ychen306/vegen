; RUN: %opt -gslp %s -S | FileCheck %s

; CHECK:  %cmp = fcmp ogt float %x, %y
; CHECK-NEXT:  br i1 %cmp, label %[[TRUE:.*]], label %[[FALSE:.*]]

; CHECK: [[TRUE]]:
; CHECK-NEXT:   [[B0:%.*]] = load <4 x float>, <4 x float>* bitcast ([8 x float]* @b to <4 x float>*)
; CHECK-NEXT:   [[C0:%.*]] = load <4 x float>, <4 x float>* bitcast ([8 x float]* @c to <4 x float>*)
; CHECK-NEXT:   [[A0:%.*]] = fadd <4 x float> [[B0]], [[C0]]
; CHECK-NEXT:   br label %[[JOIN:.*]]

; CHECK: [[FALSE]]:
; CHECK-NEXT:   [[B1:%.*]] = load <4 x float>, <4 x float>* bitcast (float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 4) to <4 x float>*)
; CHECK-NEXT:   [[C1:%.*]] = load <4 x float>, <4 x float>* bitcast (float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 4) to <4 x float>*)
; CHECK-NEXT:   [[A1:%.*]] = fsub <4 x float> [[B1]], [[C1]]
; CHECK-NEXT:   br label %[[JOIN:.*]]

; CHECK: [[JOIN]]:
; CHECK-NEXT:   [[PHI:%.*]] = phi <4 x float> [ [[A0]], %[[TRUE]] ], [ [[A1]], %[[FALSE]] ]
; CHECK-NEXT:   store <4 x float> [[PHI]], <4 x float>* bitcast ([4 x float]* @a to <4 x float>*)
; CHECK-NEXT:   ret void


source_filename = "phi.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@b = dso_local local_unnamed_addr global [8 x float] zeroinitializer, align 16
@c = dso_local local_unnamed_addr global [8 x float] zeroinitializer, align 16
@a = dso_local local_unnamed_addr global [4 x float] zeroinitializer, align 16

; Function Attrs: nofree norecurse nounwind ssp uwtable willreturn
define dso_local void @foo(float %x, float %y) local_unnamed_addr #0 {
entry:
  %cmp = fcmp ogt float %x, %y
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %0 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 0), align 16, !tbaa !3
  %1 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 0), align 16, !tbaa !3
  %add = fadd float %0, %1
  %2 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 1), align 4, !tbaa !3
  %3 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 1), align 4, !tbaa !3
  %add1 = fadd float %2, %3
  %4 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 2), align 8, !tbaa !3
  %5 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 2), align 8, !tbaa !3
  %add2 = fadd float %4, %5
  %6 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 3), align 4, !tbaa !3
  %7 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 3), align 4, !tbaa !3
  %add3 = fadd float %6, %7
  br label %if.end

if.else:                                          ; preds = %entry
  %8 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 4), align 16, !tbaa !3
  %9 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 4), align 16, !tbaa !3
  %sub = fsub float %8, %9
  %10 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 5), align 4, !tbaa !3
  %11 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 5), align 4, !tbaa !3
  %sub4 = fsub float %10, %11
  %12 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 6), align 8, !tbaa !3
  %13 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 6), align 8, !tbaa !3
  %sub5 = fsub float %12, %13
  %14 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 7), align 4, !tbaa !3
  %15 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 7), align 4, !tbaa !3
  %sub6 = fsub float %14, %15
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %a1.0 = phi float [ %add, %if.then ], [ %sub, %if.else ]
  %a2.0 = phi float [ %add1, %if.then ], [ %sub4, %if.else ]
  %a3.0 = phi float [ %add2, %if.then ], [ %sub5, %if.else ]
  %a4.0 = phi float [ %add3, %if.then ], [ %sub6, %if.else ]
  store float %a1.0, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 0), align 16, !tbaa !3
  store float %a2.0, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 1), align 4, !tbaa !3
  store float %a3.0, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 2), align 8, !tbaa !3
  store float %a4.0, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 3), align 4, !tbaa !3
  ret void
}

attributes #0 = { nofree norecurse nounwind ssp uwtable willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"float", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
