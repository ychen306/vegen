; RUN: %opt %s -gslp -o /dev/null
; RUN: %opt %s -gslp -o %t -S && %check-function  3 'int foo(int, int*, int*, int*)' 'foo(12, %%s, %%s, %%s)' %t %s

source_filename = "int-matmul.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* noalias nocapture readonly %a, i32* noalias nocapture readonly %b, i32* noalias nocapture %c) local_unnamed_addr #0 {
entry:
  %0 = zext i32 %n to i64
  %cmp50 = icmp sgt i32 %n, 0
  br i1 %cmp50, label %for.cond1.preheader.lr.ph, label %for.cond.cleanup

for.cond1.preheader.lr.ph:                        ; preds = %entry
  %wide.trip.count60 = zext i32 %n to i64
  br label %for.cond1.preheader

for.cond1.preheader:                              ; preds = %for.cond.cleanup3, %for.cond1.preheader.lr.ph
  %indvars.iv58 = phi i64 [ 0, %for.cond1.preheader.lr.ph ], [ %indvars.iv.next59, %for.cond.cleanup3 ]
  %1 = mul nuw nsw i64 %indvars.iv58, %0
  %arrayidx = getelementptr inbounds i32, i32* %a, i64 %1
  %arrayidx16 = getelementptr inbounds i32, i32* %c, i64 %1
  %wide.trip.count56 = zext i32 %n to i64
  br label %for.cond5.preheader

for.cond.cleanup.loopexit:                        ; preds = %for.cond.cleanup3
  br label %for.cond.cleanup

for.cond.cleanup:                                 ; preds = %for.cond.cleanup.loopexit, %entry
  ret void

for.cond5.preheader:                              ; preds = %for.cond5.for.cond.cleanup7_crit_edge, %for.cond1.preheader
  %indvars.iv54 = phi i64 [ 0, %for.cond1.preheader ], [ %indvars.iv.next55, %for.cond5.for.cond.cleanup7_crit_edge ]
  %arrayidx18 = getelementptr inbounds i32, i32* %arrayidx16, i64 %indvars.iv54
  %arrayidx18.promoted = load i32, i32* %arrayidx18, align 4, !tbaa !3
  %wide.trip.count = zext i32 %n to i64
  br label %for.body8

for.cond.cleanup3:                                ; preds = %for.cond5.for.cond.cleanup7_crit_edge
  %indvars.iv.next59 = add nuw nsw i64 %indvars.iv58, 1
  %exitcond61.not = icmp eq i64 %indvars.iv.next59, %wide.trip.count60
  br i1 %exitcond61.not, label %for.cond.cleanup.loopexit, label %for.cond1.preheader, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge:            ; preds = %for.body8
  %add.lcssa = phi i32 [ %add, %for.body8 ]
  store i32 %add.lcssa, i32* %arrayidx18, align 4, !tbaa !3
  %indvars.iv.next55 = add nuw nsw i64 %indvars.iv54, 1
  %exitcond57.not = icmp eq i64 %indvars.iv.next55, %wide.trip.count56
  br i1 %exitcond57.not, label %for.cond.cleanup3, label %for.cond5.preheader, !llvm.loop !10

for.body8:                                        ; preds = %for.body8, %for.cond5.preheader
  %indvars.iv = phi i64 [ 0, %for.cond5.preheader ], [ %indvars.iv.next, %for.body8 ]
  %add53 = phi i32 [ %arrayidx18.promoted, %for.cond5.preheader ], [ %add, %for.body8 ]
  %arrayidx10 = getelementptr inbounds i32, i32* %arrayidx, i64 %indvars.iv
  %2 = load i32, i32* %arrayidx10, align 4, !tbaa !3
  %3 = mul nuw nsw i64 %indvars.iv, %0
  %arrayidx12 = getelementptr inbounds i32, i32* %b, i64 %indvars.iv54
  %arrayidx14 = getelementptr inbounds i32, i32* %arrayidx12, i64 %3
  %4 = load i32, i32* %arrayidx14, align 4, !tbaa !3
  %mul = mul nsw i32 %4, %2
  %add = add nsw i32 %add53, %mul
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %for.cond5.for.cond.cleanup7_crit_edge, label %for.body8, !llvm.loop !11
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

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
!11 = distinct !{!11, !8, !9}
