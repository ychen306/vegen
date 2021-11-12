; RUN: %opt -gslp -no-unroll %s -S | FileCheck %s

; CHECK:  [[X_ADDR:%.*]] = bitcast float* %x to <4 x float>*
; CHECK-NEXT:  [[X:%.*]] = load <4 x float>, <4 x float>* [[X_ADDR]]
; CHECK-NEXT:  [[FNEG:%.*]] = fneg <4 x float> [[X]]
; CHECK-NEXT:  [[Y_ADDR:%.*]] = bitcast float* %y to <4 x float>*
; CHECK-NEXT:  store <4 x float> [[FNEG]], <4 x float>* [[Y_ADDR]]
; CHECK-NEXT:  ret void

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(float* noalias nocapture %y, float* noalias nocapture readonly %x) local_unnamed_addr #0 {
entry:
  %0 = load float, float* %x, align 4, !tbaa !3
  %fneg = fneg float %0
  store float %fneg, float* %y, align 4, !tbaa !3
  %arrayidx.1 = getelementptr inbounds float, float* %x, i64 1
  %1 = load float, float* %arrayidx.1, align 4, !tbaa !3
  %fneg.1 = fneg float %1
  %arrayidx2.1 = getelementptr inbounds float, float* %y, i64 1
  store float %fneg.1, float* %arrayidx2.1, align 4, !tbaa !3
  %arrayidx.2 = getelementptr inbounds float, float* %x, i64 2
  %2 = load float, float* %arrayidx.2, align 4, !tbaa !3
  %fneg.2 = fneg float %2
  %arrayidx2.2 = getelementptr inbounds float, float* %y, i64 2
  store float %fneg.2, float* %arrayidx2.2, align 4, !tbaa !3
  %arrayidx.3 = getelementptr inbounds float, float* %x, i64 3
  %3 = load float, float* %arrayidx.3, align 4, !tbaa !3
  %fneg.3 = fneg float %3
  %arrayidx2.3 = getelementptr inbounds float, float* %y, i64 3
  store float %fneg.3, float* %arrayidx2.3, align 4, !tbaa !3
  ret void
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"float", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
