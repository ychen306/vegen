; RUN: %opt -gslp -no-unroll %s -S | FileCheck %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; CHECK:  %0 = bitcast float* %b to <4 x float>*
; CHECK-NEXT:  %1 = load <4 x float>, <4 x float>* %0
; CHECK-NEXT:  %2 = fadd <4 x float> %1, <float 1.000000e+00, float 1.000000e+00, float 1.000000e+00, float 1.000000e+00>
; CHECK-NEXT:  %3 = call <4 x float> @llvm.sin.v4f32(<4 x float> %2)
; CHECK-NEXT:  %4 = fadd <4 x float> %3, <float 2.000000e+00, float 2.000000e+00, float 2.000000e+00, float 2.000000e+00>
; CHECK-NEXT:  %5 = bitcast float* %a to <4 x float>*
; CHECK-NEXT:  store <4 x float> %4, <4 x float>* %5
; CHECK-NEXT:  ret void

; Function Attrs: nofree nounwind ssp uwtable
define dso_local void @foo(float* noalias nocapture %a, float* noalias nocapture readonly %b) local_unnamed_addr #0 {
entry:
  %0 = load float, float* %b, align 4, !tbaa !3
  %add = fadd float %0, 1.000000e+00
  %1 = call float @llvm.sin.f32(float %add)
  %add1 = fadd float %1, 2.000000e+00
  store float %add1, float* %a, align 4, !tbaa !3
  %arrayidx.1 = getelementptr inbounds float, float* %b, i64 1
  %2 = load float, float* %arrayidx.1, align 4, !tbaa !3
  %add.1 = fadd float %2, 1.000000e+00
  %3 = call float @llvm.sin.f32(float %add.1)
  %add1.1 = fadd float %3, 2.000000e+00
  %arrayidx3.1 = getelementptr inbounds float, float* %a, i64 1
  store float %add1.1, float* %arrayidx3.1, align 4, !tbaa !3
  %arrayidx.2 = getelementptr inbounds float, float* %b, i64 2
  %4 = load float, float* %arrayidx.2, align 4, !tbaa !3
  %add.2 = fadd float %4, 1.000000e+00
  %5 = call float @llvm.sin.f32(float %add.2)
  %add1.2 = fadd float %5, 2.000000e+00
  %arrayidx3.2 = getelementptr inbounds float, float* %a, i64 2
  store float %add1.2, float* %arrayidx3.2, align 4, !tbaa !3
  %arrayidx.3 = getelementptr inbounds float, float* %b, i64 3
  %6 = load float, float* %arrayidx.3, align 4, !tbaa !3
  %add.3 = fadd float %6, 1.000000e+00
  %7 = call float @llvm.sin.f32(float %add.3)
  %add1.3 = fadd float %7, 2.000000e+00
  %arrayidx3.3 = getelementptr inbounds float, float* %a, i64 3
  store float %add1.3, float* %arrayidx3.3, align 4, !tbaa !3
  ret void
}

; Function Attrs: nofree nosync nounwind readnone speculatable willreturn
declare float @llvm.sin.f32(float) #1

attributes #0 = { nofree nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nofree nosync nounwind readnone speculatable willreturn }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"float", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
