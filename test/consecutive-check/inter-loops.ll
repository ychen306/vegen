; RUN: %opt -test-consecutive-check %s -o /dev/null 2>&1 | FileCheck %s

; CHECK: load i32, i32* %arrayidx{{.*}}load i32, i32* %arrayidx9{{.*}} are consecutive

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* nocapture %a, i32* nocapture readonly %b, i32* nocapture readnone %c) local_unnamed_addr #0 {
entry:
  %cmp28 = icmp sgt i32 %n, 0
  br i1 %cmp28, label %for.body.preheader, label %for.cond4.preheader

for.body.preheader:                               ; preds = %entry
  %wide.trip.count34 = zext i32 %n to i64
  br label %for.body

for.cond4.preheader:                              ; preds = %for.body, %entry
  %cmp526 = icmp sgt i32 %n, 0
  br i1 %cmp526, label %for.body7.preheader, label %for.cond.cleanup6

for.body7.preheader:                              ; preds = %for.cond4.preheader
  %wide.trip.count = zext i32 %n to i64
  br label %for.body7

for.body:                                         ; preds = %for.body.preheader, %for.body
  %indvars.iv32 = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next33, %for.body ]
  %arrayidx = getelementptr inbounds i32, i32* %b, i64 %indvars.iv32
  %0 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %arrayidx2 = getelementptr inbounds i32, i32* %a, i64 %indvars.iv32
  store i32 %0, i32* %arrayidx2, align 4, !tbaa !3
  %indvars.iv.next33 = add nuw nsw i64 %indvars.iv32, 1
  %exitcond35.not = icmp eq i64 %indvars.iv.next33, %wide.trip.count34
  br i1 %exitcond35.not, label %for.cond4.preheader, label %for.body, !llvm.loop !7

for.cond.cleanup6:                                ; preds = %for.body7, %for.cond4.preheader
  ret void

for.body7:                                        ; preds = %for.body7.preheader, %for.body7
  %indvars.iv = phi i64 [ 0, %for.body7.preheader ], [ %indvars.iv.next, %for.body7 ]
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %arrayidx9 = getelementptr inbounds i32, i32* %b, i64 %indvars.iv.next
  %1 = load i32, i32* %arrayidx9, align 4, !tbaa !3
  %arrayidx11 = getelementptr inbounds i32, i32* %a, i64 %indvars.iv
  store i32 %1, i32* %arrayidx11, align 4, !tbaa !3
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %for.cond.cleanup6, label %for.body7, !llvm.loop !10
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
