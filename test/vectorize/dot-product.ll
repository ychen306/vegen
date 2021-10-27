; RUN: %opt -gslp -no-unroll %s -S | FileCheck %s

; CHECK:   %cmp56 = icmp sgt i32 %n, 0
; CHECK-NEXT:   br i1 %cmp56, label %[[PREHEADER:.*]], label %[[NO_LOOP:.*]]

; CHECK: [[PREHEADER]]:
; CHECK-NEXT:   %wide.trip.count = zext i32 %n to i64
; CHECK-NEXT:   br label %[[HEADER:.*]]

; CHECK: [[NO_LOOP]]:
; CHECK-NEXT:   br label %[[JOIN:.*]]

; CHECK: [[HEADER]]:
; CHECK-NEXT:   [[VSUM:%.*]] = phi <4 x float> [ zeroinitializer, %0 ], [ [[VSUM_NEXT:%.*]], %[[LATCH:.*]] ]
; CHECK-NEXT:   [[IDX:%.*]] = phi i64 [ 0, %[[PREHEADER]] ], [ %indvars.iv.next, %[[LATCH]] ]
; CHECK-NEXT:   [[IDX4:%.*]] = shl nsw i64 %3, 2
; CHECK-NEXT:   %arrayidx = getelementptr inbounds float, float* %a, i64 [[IDX4]]
; CHECK-NEXT:   [[A_ADDR:%.*]] = bitcast float* %arrayidx to <4 x float>*
; CHECK-NEXT:   [[A:%.*]] = load <4 x float>, <4 x float>* [[A_ADDR]], align 4, !tbaa !3
; CHECK-NEXT:   %arrayidx3 = getelementptr inbounds float, float* %b, i64 [[IDX4]]
; CHECK-NEXT:   [[B_ADDR:%.*]] = bitcast float* %arrayidx3 to <4 x float>*
; CHECK-NEXT:   [[B:%.*]] = load <4 x float>, <4 x float>* [[B_ADDR]], align 4, !tbaa !3
; CHECK-NEXT:   [[VMUL:%.*]] = fmul <4 x float> [[A]], [[B]]
; CHECK-NEXT:   %indvars.iv.next = add nuw nsw i64 %3, 1
; CHECK-NEXT:   [[SHOULD_BREAK:%.*]] = icmp eq i64 %indvars.iv.next, %wide.trip.count
; CHECK-NEXT:   br i1 [[SHOULD_BREAK]], label %[[IF_TRUE:.*]], label %[[IF_FALSE:.*]]

; CHECK: [[LATCH]]:
; CHECK-NEXT:   [[VSUM_NEXT]] = fadd <4 x float> [[VSUM]], [[VMUL]]
; CHECK-NEXT:   br i1 [[CONT:%.*]], label %[[HEADER]], label %[[EXIT:.*]]

; CHECK: [[EXIT]]:
; CHECK-NEXT:   [[REDUCED:%.*]] = call float @llvm.vector.reduce.fadd.v4f32(float -0.000000e+00, <4 x float> [[VSUM_NEXT]])
; CHECK-NEXT:   [[REDUCED2:%.*]] = fadd float [[REDUCED]], 0.000000e+00
; CHECK-NEXT:   br label %[[JOIN]]

; CHECK: [[IF_TRUE]]:
; CHECK-NEXT:   br label %[[MERGE:.*]]

; CHECK: [[IF_FALSE]]:
; CHECK-NEXT:   br label %[[MERGE]]

; CHECK: [[MERGE]]:
; CHECK-NEXT:   [[CONT]] = phi i1 [ false, %[[IF_TRUE]] ], [ true, %[[IF_FALSE]] ]

; CHECK: [[JOIN]]:
; CHECK-NEXT:   [[PHI:%.*]] = phi float [ [[REDUCED2]], %[[EXIT]] ], [ 0.000000e+00, %[[NO_LOOP]] ]
; CHECK-NEXT:   ret float [[PHI]]

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: norecurse nounwind readonly ssp uwtable
define dso_local float @reduce(i32 %n, float* nocapture readonly %a, float* nocapture readonly %b) local_unnamed_addr #0 {
entry:
  %cmp56 = icmp sgt i32 %n, 0
  br i1 %cmp56, label %for.body.preheader, label %for.cond.cleanup

for.body.preheader:                               ; preds = %entry
  %wide.trip.count = zext i32 %n to i64
  br label %for.body

for.cond.cleanup.loopexit:                        ; preds = %for.body
  br label %for.cond.cleanup

for.cond.cleanup:                                 ; preds = %for.cond.cleanup.loopexit, %entry
  %sum.0.lcssa = phi float [ 0.000000e+00, %entry ], [ %add34, %for.cond.cleanup.loopexit ]
  ret float %sum.0.lcssa

for.body:                                         ; preds = %for.body, %for.body.preheader
  %indvars.iv = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next, %for.body ]
  %sum.057 = phi float [ 0.000000e+00, %for.body.preheader ], [ %add34, %for.body ]
  %0 = shl nsw i64 %indvars.iv, 2
  %arrayidx = getelementptr inbounds float, float* %a, i64 %0
  %1 = load float, float* %arrayidx, align 4, !tbaa !3
  %arrayidx3 = getelementptr inbounds float, float* %b, i64 %0
  %2 = load float, float* %arrayidx3, align 4, !tbaa !3
  %mul4 = fmul float %1, %2
  %add = fadd float %sum.057, %mul4
  %3 = or i64 %0, 1
  %arrayidx8 = getelementptr inbounds float, float* %a, i64 %3
  %4 = load float, float* %arrayidx8, align 4, !tbaa !3
  %arrayidx12 = getelementptr inbounds float, float* %b, i64 %3
  %5 = load float, float* %arrayidx12, align 4, !tbaa !3
  %mul13 = fmul float %4, %5
  %add14 = fadd float %add, %mul13
  %6 = or i64 %0, 2
  %arrayidx18 = getelementptr inbounds float, float* %a, i64 %6
  %7 = load float, float* %arrayidx18, align 4, !tbaa !3
  %arrayidx22 = getelementptr inbounds float, float* %b, i64 %6
  %8 = load float, float* %arrayidx22, align 4, !tbaa !3
  %mul23 = fmul float %7, %8
  %add24 = fadd float %add14, %mul23
  %9 = or i64 %0, 3
  %arrayidx28 = getelementptr inbounds float, float* %a, i64 %9
  %10 = load float, float* %arrayidx28, align 4, !tbaa !3
  %arrayidx32 = getelementptr inbounds float, float* %b, i64 %9
  %11 = load float, float* %arrayidx32, align 4, !tbaa !3
  %mul33 = fmul float %10, %11
  %add34 = fadd float %add24, %mul33
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %for.cond.cleanup.loopexit, label %for.body, !llvm.loop !7
}

attributes #0 = { norecurse nounwind readonly ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"float", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = distinct !{!7, !8, !9}
!8 = !{!"llvm.loop.mustprogress"}
!9 = !{!"llvm.loop.unroll.disable"}
