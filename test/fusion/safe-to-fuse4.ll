; RUN: %test-loop-fusion %s | FileCheck %s
; CHECK: {{[[:space:]]+}}safe

; This is basically the same as unsafe-to-fuse6 but we replace the use
; of %cond with the constant 4 in the second loop (and keep the in-between joins)
; This is to test that the safety works on loops with in-between blocks

; ModuleID = 'unsafe-to-fuse6.c'
source_filename = "unsafe-to-fuse6.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* noalias nocapture readonly %x, i32* noalias nocapture %y, i32* nocapture %t1, i32* nocapture readonly %t2) local_unnamed_addr #0 {
entry:
  %cmp23 = icmp sgt i32 %n, 0
  br i1 %cmp23, label %for.body.preheader, label %for.cond.cleanup

for.body.preheader:                               ; preds = %entry
  %wide.trip.count28 = zext i32 %n to i64
  br label %for.body

for.cond.cleanup:                                 ; preds = %for.body, %entry
  %s.0.lcssa = phi i32 [ 0, %entry ], [ %add, %for.body ]
  store i32 %s.0.lcssa, i32* %t1, align 4, !tbaa !3
  %0 = load i32, i32* %t2, align 4, !tbaa !3
  %tobool.not = icmp eq i32 %0, 0
  br i1 %tobool.not, label %get_45, label %get_34

get_45:
  br label %join

get_34:
  br label %join

join:
  %cond = phi i32 [45, %get_45], [34, %get_34]
  %cmp321 = icmp sgt i32 %n, 0
  store i32 %cond, i32* %t2
  br i1 %cmp321, label %for.body5.preheader, label %for.cond.cleanup4

for.body5.preheader:                              ; preds = %for.cond.cleanup
  %wide.trip.count = zext i32 %n to i64
  br label %for.body5

for.body:                                         ; preds = %for.body.preheader, %for.body
  %indvars.iv26 = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next27, %for.body ]
  %s.025 = phi i32 [ 0, %for.body.preheader ], [ %add, %for.body ]
  %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv26
  %1 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %add = add nsw i32 %1, %s.025
  %indvars.iv.next27 = add nuw nsw i64 %indvars.iv26, 1
  %exitcond29.not = icmp eq i64 %indvars.iv.next27, %wide.trip.count28
  br i1 %exitcond29.not, label %for.cond.cleanup, label %for.body, !llvm.loop !7

for.cond.cleanup4:                                ; preds = %for.body5, %for.cond.cleanup
  ret void

for.body5:                                        ; preds = %for.body5.preheader, %for.body5
  %indvars.iv = phi i64 [ 0, %for.body5.preheader ], [ %indvars.iv.next, %for.body5 ]
  %arrayidx7 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
  %2 = load i32, i32* %arrayidx7, align 4, !tbaa !3
  %mul = mul nsw i32 %2, 4
  store i32 %mul, i32* %arrayidx7, align 4, !tbaa !3
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %for.cond.cleanup4, label %for.body5, !llvm.loop !10
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
