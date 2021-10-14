; RUN: %opt -gslp -reschedule-scalar %s -S | FileCheck %s

; CHECK:  %cmp = fcmp ogt float %x, %y
; CHECK-NEXT:  br i1 %cmp, label %[[TRUE:.*]], label %[[FALSE:.*]]

; CHECK:[[TRUE]]:
; CHECK-NEXT:  %1 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 0)
; CHECK-NEXT:  %2 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 0)
; CHECK-NEXT:  %add = fadd float %1, %2
; CHECK-NEXT:  br label %[[JOIN:.*]]

; CHECK:[[FALSE]]:
; CHECK-NEXT:  %4 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 4)
; CHECK-NEXT:  %5 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 4)
; CHECK-NEXT:  %sub = fsub float %4, %5
; CHECK-NEXT:  br label %[[JOIN]]

; CHECK:[[JOIN]]:
; CHECK-NEXT:  %demoted{{.*}} = phi float [ %add, %0 ], [ %sub, %3 ]
; CHECK-NEXT:  store float %demoted.0, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 0)
; CHECK-NEXT:  ret void


source_filename = "scalar-phi.c"
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
  br label %if.end

if.else:                                          ; preds = %entry
  %2 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @b, i64 0, i64 4), align 16, !tbaa !3
  %3 = load float, float* getelementptr inbounds ([8 x float], [8 x float]* @c, i64 0, i64 4), align 16, !tbaa !3
  %sub = fsub float %2, %3
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %a1.0 = phi float [ %add, %if.then ], [ %sub, %if.else ]
  store float %a1.0, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 0), align 16, !tbaa !3
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
