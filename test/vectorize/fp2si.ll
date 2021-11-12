; RUN: %opt -gslp -no-unroll %s -S | FileCheck %s

; CHECK:  [[X_ADDR:%.*]] = bitcast float* %x to <4 x float>*
; CHECK-NEXT:  [[X:%.*]] = load <4 x float>, <4 x float>* [[X_ADDR]]
; CHECK-NEXT:  [[CONV:%.*]] = fptosi <4 x float> [[X]] to <4 x i32>
; CHECK-NEXT:  [[Y_ADDR:%.*]] = bitcast i32* %y to <4 x i32>*
; CHECK-NEXT:  store <4 x i32> [[CONV]], <4 x i32>* [[Y_ADDR]]
; CHECK-NEXT:  ret void

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32* noalias nocapture %y, float* noalias nocapture readonly %x) local_unnamed_addr #0 {
entry:
  %0 = load float, float* %x, align 4, !tbaa !3
  %conv = fptosi float %0 to i32
  store i32 %conv, i32* %y, align 4, !tbaa !7
  %arrayidx.1 = getelementptr inbounds float, float* %x, i64 1
  %1 = load float, float* %arrayidx.1, align 4, !tbaa !3
  %conv.1 = fptosi float %1 to i32
  %arrayidx2.1 = getelementptr inbounds i32, i32* %y, i64 1
  store i32 %conv.1, i32* %arrayidx2.1, align 4, !tbaa !7
  %arrayidx.2 = getelementptr inbounds float, float* %x, i64 2
  %2 = load float, float* %arrayidx.2, align 4, !tbaa !3
  %conv.2 = fptosi float %2 to i32
  %arrayidx2.2 = getelementptr inbounds i32, i32* %y, i64 2
  store i32 %conv.2, i32* %arrayidx2.2, align 4, !tbaa !7
  %arrayidx.3 = getelementptr inbounds float, float* %x, i64 3
  %3 = load float, float* %arrayidx.3, align 4, !tbaa !3
  %conv.3 = fptosi float %3 to i32
  %arrayidx2.3 = getelementptr inbounds i32, i32* %y, i64 3
  store i32 %conv.3, i32* %arrayidx2.3, align 4, !tbaa !7
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
!7 = !{!8, !8, i64 0}
!8 = !{!"int", !5, i64 0}
