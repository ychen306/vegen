; RUN: %opt -gslp -no-unroll %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@aa = external dso_local local_unnamed_addr global [256 x [256 x float]], align 16

define dso_local void @s114() local_unnamed_addr #0 {
entry:
  br label %for.cond1.preheader

for.cond1.preheader:                              ; preds = %for.cond.cleanup3, %entry
  br label %for.cond5.preheader

for.cond.cleanup:                                 ; preds = %for.cond.cleanup3
  ret void

for.cond5.preheader:                              ; preds = %for.cond.cleanup7, %for.cond1.preheader
  %indvars.iv43 = phi i64 [ 0, %for.cond1.preheader ], [ undef, %for.cond.cleanup7 ]
  br i1 undef, label %for.cond.cleanup7, label %for.body8.lr.ph

for.body8.lr.ph:                                  ; preds = %for.cond5.preheader
  br i1 undef, label %for.cond.cleanup7.loopexit.unr-lcssa, label %for.body8.lr.ph.new

for.body8.lr.ph.new:                              ; preds = %for.body8.lr.ph
  br label %for.body8

for.cond.cleanup3:                                ; preds = %for.cond.cleanup7
  br i1 undef, label %for.cond.cleanup, label %for.cond1.preheader, !llvm.loop !0

for.cond.cleanup7.loopexit.unr-lcssa.loopexit:    ; preds = %for.body8
  br label %for.cond.cleanup7.loopexit.unr-lcssa

for.cond.cleanup7.loopexit.unr-lcssa:             ; preds = %for.cond.cleanup7.loopexit.unr-lcssa.loopexit, %for.body8.lr.ph
  br label %for.cond.cleanup7

for.cond.cleanup7:                                ; preds = %for.cond.cleanup7.loopexit.unr-lcssa, %for.cond5.preheader
  br i1 undef, label %for.cond.cleanup3, label %for.cond5.preheader, !llvm.loop !3

for.body8:                                        ; preds = %for.body8, %for.body8.lr.ph.new
  %indvars.iv = phi i64 [ 0, %for.body8.lr.ph.new ], [ undef, %for.body8 ]
  %indvars.iv.next.1 = or i64 %indvars.iv, 2
  %arrayidx10.2 = getelementptr inbounds [256 x [256 x float]], [256 x [256 x float]]* @aa, i64 0, i64 %indvars.iv.next.1, i64 %indvars.iv43
  %0 = load float, float* %arrayidx10.2, align 4, !tbaa !4
  %add.2 = fadd float %0, undef
  %arrayidx18.2 = getelementptr inbounds [256 x [256 x float]], [256 x [256 x float]]* @aa, i64 0, i64 %indvars.iv43, i64 %indvars.iv.next.1
  store float %add.2, float* %arrayidx18.2, align 8, !tbaa !4
  %indvars.iv.next.2 = or i64 %indvars.iv, 3
  %arrayidx10.3 = getelementptr inbounds [256 x [256 x float]], [256 x [256 x float]]* @aa, i64 0, i64 %indvars.iv.next.2, i64 %indvars.iv43
  %1 = load float, float* %arrayidx10.3, align 4, !tbaa !4
  %add.3 = fadd float %1, undef
  %arrayidx18.3 = getelementptr inbounds [256 x [256 x float]], [256 x [256 x float]]* @aa, i64 0, i64 %indvars.iv43, i64 %indvars.iv.next.2
  store float %add.3, float* %arrayidx18.3, align 4, !tbaa !4
  br i1 undef, label %for.cond.cleanup7.loopexit.unr-lcssa.loopexit, label %for.body8, !llvm.loop !8
}

attributes #0 = { "target-cpu"="penryn" }

!0 = distinct !{!0, !1, !2}
!1 = !{!"llvm.loop.mustprogress"}
!2 = !{!"llvm.loop.unroll.disable"}
!3 = distinct !{!3, !1, !2}
!4 = !{!5, !5, i64 0}
!5 = !{!"float", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C/C++ TBAA"}
!8 = distinct !{!8, !1, !2}
