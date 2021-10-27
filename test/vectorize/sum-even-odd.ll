; RUN: %opt -gslp -no-unroll %s -o - -S | FileCheck %s

; CHECK:   [[POS:%.*]] = icmp slt i32 0, %n
; CHECK-NEXT:   br i1 [[POS]], label %[[PREHEADER:.*]], label %[[SKIP:.*]]

; CHECK: [[PREHEADER]]:
; CHECK-NEXT:   %arrayidx1 = getelementptr inbounds i32, i32* %a, i64 0
; CHECK-NEXT:   [[ADDR:%.*]] = bitcast i32* %arrayidx1 to <2 x i32>*
; CHECK-NEXT:   [[INIT:%.*]] = load <2 x i32>, <2 x i32>* [[ADDR]], align 4, !tbaa !3
; CHECK-NEXT:   br label %[[HEADER:.*]]

; CHECK: [[SKIP]]:
; CHECK-NEXT:   br label %[[DONE:.*]]

; CHECK: [[HEADER]]:
; CHECK-NEXT:   [[IDX0:%.*]] = phi i32 [ 0, %0 ], [ [[IDX0_NEXT:%.*]], %[[LATCH:.*]] ]
; CHECK-NEXT:   [[IDX1:%.*]] = phi i32 [ 0, %0 ], [ [[IDX1_NEXT:%.*]], %[[LATCH]] ]
; CHECK-NEXT:   [[SUM_PHI:%.*]] = phi <2 x i32> [ [[INIT]], %0 ], [ [[ITER:%.*]], %[[LATCH]] ]
; CHECK-NEXT:   %mul = mul nsw i32 2, [[IDX1]]
; CHECK-NEXT:   %idxprom = sext i32 %mul to i64
; CHECK-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %b, i64 %idxprom
; CHECK-NEXT:   [[ADDR_LOOP:%.*]] = bitcast i32* %arrayidx to <2 x i32>*
; CHECK-NEXT:   [[LOAD:%.*]] = load <2 x i32>, <2 x i32>* [[ADDR_LOOP]], align 4, !tbaa !3
; CHECK-NEXT:   [[SUM:%.*]] = add <2 x i32> [[SUM_PHI]], [[LOAD]]
; CHECK-DAG:    [[IDX1_NEXT]] = add nsw i32 [[IDX1]], 1
; CHECK-DAG:    [[LT_N:%.*]] = icmp slt i32 %inc, %n
; CHECK-DAG:    [[IDX0_NEXT]] = add nsw i32 [[IDX0]], 1
; CHECK-NEXT:   br i1 [[LT_N]], label %[[IF_TRUE:.*]], label %[[IF_FALSE:.*]]

; CHECK: [[LATCH]]:
; CHECK-NEXT:  br i1 [[CONT:%.*]], label %[[HEADER]], label %[[EXIT:.*]]

; CHECK: [[EXIT]]:
; CHECK-NEXT:   [[OUT_ADDR:%.*]] = bitcast i32* %arrayidx1 to <2 x i32>*
; CHECK-NEXT:   store <2 x i32> [[SUM]], <2 x i32>* [[OUT_ADDR]], align 4, !tbaa !3
; CHECK-NEXT:   br label %[[DONE]]

; CHECK: [[IF_TRUE]]:
; CHECK-NEXT:   br label %[[MERGE:.*]]

; CHECK: [[IF_FALSE]]:
; CHECK-NEXT:   br label %[[MERGE]]

; CHECK: [[MERGE]]:
; CHECK-NEXT: [[CONT]] = phi i1 [ true, %[[IF_TRUE]] ], [ false, %[[IF_FALSE]] ]

; CHECK: [[DONE]]:
; CHECK-NEXT:   ret void

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* noalias %a, i32* noalias %b) #0 {
entry:
  %cmp3 = icmp slt i32 0, %n
  br i1 %cmp3, label %for.body.lr.ph, label %for.cond.cleanup

for.body.lr.ph:                                   ; preds = %entry
  %arrayidx1 = getelementptr inbounds i32, i32* %a, i64 0
  %arrayidx1.promoted = load i32, i32* %arrayidx1, align 4, !tbaa !3
  br label %for.body

for.cond.for.cond.cleanup_crit_edge:              ; preds = %for.inc
  %add.lcssa = phi i32 [ %add, %for.inc ]
  store i32 %add.lcssa, i32* %arrayidx1, align 4, !tbaa !3
  br label %for.cond.cleanup

for.cond.cleanup:                                 ; preds = %for.cond.for.cond.cleanup_crit_edge, %entry
  br label %for.end

for.body:                                         ; preds = %for.inc, %for.body.lr.ph
  %add2 = phi i32 [ %arrayidx1.promoted, %for.body.lr.ph ], [ %add, %for.inc ]
  %i.04 = phi i32 [ 0, %for.body.lr.ph ], [ %inc, %for.inc ]
  %mul = mul nsw i32 2, %i.04
  %idxprom = sext i32 %mul to i64
  %arrayidx = getelementptr inbounds i32, i32* %b, i64 %idxprom
  %0 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %add = add nsw i32 %add2, %0
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.04, 1
  %cmp = icmp slt i32 %inc, %n
  br i1 %cmp, label %for.body, label %for.cond.for.cond.cleanup_crit_edge, !llvm.loop !7

for.end:                                          ; preds = %for.cond.cleanup
  %cmp41 = icmp slt i32 0, %n
  br i1 %cmp41, label %for.body6.lr.ph, label %for.cond.cleanup5

for.body6.lr.ph:                                  ; preds = %for.end
  %arrayidx11 = getelementptr inbounds i32, i32* %a, i64 1
  %arrayidx11.promoted = load i32, i32* %arrayidx11, align 4, !tbaa !3
  br label %for.body6

for.cond3.for.cond.cleanup5_crit_edge:            ; preds = %for.inc13
  %add12.lcssa = phi i32 [ %add12, %for.inc13 ]
  store i32 %add12.lcssa, i32* %arrayidx11, align 4, !tbaa !3
  br label %for.cond.cleanup5

for.cond.cleanup5:                                ; preds = %for.cond3.for.cond.cleanup5_crit_edge, %for.end
  br label %for.end15

for.body6:                                        ; preds = %for.inc13, %for.body6.lr.ph
  %add121 = phi i32 [ %arrayidx11.promoted, %for.body6.lr.ph ], [ %add12, %for.inc13 ]
  %i2.02 = phi i32 [ 0, %for.body6.lr.ph ], [ %inc14, %for.inc13 ]
  %mul7 = mul nsw i32 2, %i2.02
  %add8 = add nsw i32 %mul7, 1
  %idxprom9 = sext i32 %add8 to i64
  %arrayidx10 = getelementptr inbounds i32, i32* %b, i64 %idxprom9
  %1 = load i32, i32* %arrayidx10, align 4, !tbaa !3
  %add12 = add nsw i32 %add121, %1
  br label %for.inc13

for.inc13:                                        ; preds = %for.body6
  %inc14 = add nsw i32 %i2.02, 1
  %cmp4 = icmp slt i32 %inc14, %n
  br i1 %cmp4, label %for.body6, label %for.cond3.for.cond.cleanup5_crit_edge, !llvm.loop !10

for.end15:                                        ; preds = %for.cond.cleanup5
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

attributes #0 = { nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nofree nosync nounwind willreturn }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = distinct !{!7, !8, !9}
!8 = !{!"llvm.loop.mustprogress"}
!9 = !{!"llvm.loop.unroll.disable"}
!10 = distinct !{!10, !8, !9}
