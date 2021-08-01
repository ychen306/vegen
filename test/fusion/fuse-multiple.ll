; RUN: %test-loop-fusion %s -fusion-group=for.body,for.body16 -fusion-group=for.body5,for.body27 | FileCheck %s
; RUN: %test-loop-fusion %s -fusion-group=for.body,for.body16 -fusion-group=for.body5,for.body27 -do-fusion | FileCheck %s --check-prefixes=DO_FUSION
; RUN: %test-loop-fusion %s -do-fusion > %t && %check-function 2 'int foo(int, int*, int*)' 'foo(1024, %%s, %%s)' %t %s

; CHECK: Fusing for.body and for.body16 is safe
; CHECK: Fusing for.body5 and for.body27 is safe

; DO_FUSION: for.body:
; DO_FUSION-NEXT:   %indvars.iv67 = phi i64 [ 0, %for.body16.preheader ], [ %indvars.iv.next68, %for.body16 ]
; DO_FUSION-NEXT:   %indvars.iv59 = phi i64 [ 0, %for.body16.preheader ], [ %indvars.iv.next60, %for.body16 ]

; DO_FUSION-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv67
; DO_FUSION-NEXT:   %0 = load i32, i32* %arrayidx, align 4
; DO_FUSION-NEXT:   %add = add nsw i32 %0, 100
; DO_FUSION-NEXT:   store i32 %add, i32* %arrayidx, align 4
; DO_FUSION-NEXT:   %indvars.iv.next68 = add nuw nsw i64 %indvars.iv67, 1
; DO_FUSION-NEXT:   %exitcond70.not = icmp eq i64 %indvars.iv.next68, %wide.trip.count69
; DO_FUSION-NEXT:   br label %for.body16

; DO_FUSION: for.body5:
; DO_FUSION-NEXT:   %indvars.iv63 = phi i64 [ 0, %for.body27.preheader ], [ %indvars.iv.next64, %for.body27 ]
; DO_FUSION-NEXT:   %indvars.iv = phi i64 [ 0, %for.body27.preheader ], [ %indvars.iv.next, %for.body27 ]

; DO_FUSION-NEXT:   %arrayidx7 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv63
; DO_FUSION-NEXT:   %1 = load i32, i32* %arrayidx7, align 4
; DO_FUSION-NEXT:   %add8 = add nsw i32 %1, 100
; DO_FUSION-NEXT:   store i32 %add8, i32* %arrayidx7, align 4
; DO_FUSION-NEXT:   %indvars.iv.next64 = add nuw nsw i64 %indvars.iv63, 1
; DO_FUSION-NEXT:   %exitcond66.not = icmp eq i64 %indvars.iv.next64, %wide.trip.count65
; DO_FUSION-NEXT:   br label %for.body27

; DO_FUSION: for.body16:
; DO_FUSION-NEXT:   %arrayidx18 = getelementptr inbounds i32, i32* %x, i64 %indvars.iv59
; DO_FUSION-NEXT:   %2 = load i32, i32* %arrayidx18, align 4
; DO_FUSION-NEXT:   %add19 = add nsw i32 %2, 100
; DO_FUSION-NEXT:   store i32 %add19, i32* %arrayidx18, align 4
; DO_FUSION-NEXT:   %indvars.iv.next60 = add nuw nsw i64 %indvars.iv59, 1
; DO_FUSION-NEXT:   %exitcond62.not = icmp eq i64 %indvars.iv.next60, %wide.trip.count61
; DO_FUSION-NEXT:   br i1 %exitcond62.not, label %for.cond2.preheader, label %for.body{{,|$}}

; DO_FUSION: for.body27:
; DO_FUSION-NEXT:   %arrayidx29 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
; DO_FUSION-NEXT:   %3 = load i32, i32* %arrayidx29, align 4
; DO_FUSION-NEXT:   %add30 = add nsw i32 %3, 100
; DO_FUSION-NEXT:   store i32 %add30, i32* %arrayidx29, align 4
; DO_FUSION-NEXT:   %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
; DO_FUSION-NEXT:   %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
; DO_FUSION-NEXT:   br i1 %exitcond.not, label %for.cond13.preheader, label %for.body5

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* nocapture %x, i32* nocapture %y) local_unnamed_addr #0 {
entry:
  %cmp57 = icmp sgt i32 %n, 0
  br i1 %cmp57, label %for.body.preheader, label %for.cond2.preheader

for.body.preheader:                               ; preds = %entry
  %wide.trip.count69 = zext i32 %n to i64
  br label %for.body

for.cond2.preheader:                              ; preds = %for.body, %entry
  %cmp355 = icmp sgt i32 %n, 0
  br i1 %cmp355, label %for.body5.preheader, label %for.cond13.preheader

for.body5.preheader:                              ; preds = %for.cond2.preheader
  %wide.trip.count65 = zext i32 %n to i64
  br label %for.body5

for.body:                                         ; preds = %for.body.preheader, %for.body
  %indvars.iv67 = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next68, %for.body ]
  %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv67
  %0 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %add = add nsw i32 %0, 100
  store i32 %add, i32* %arrayidx, align 4, !tbaa !3
  %indvars.iv.next68 = add nuw nsw i64 %indvars.iv67, 1
  %exitcond70.not = icmp eq i64 %indvars.iv.next68, %wide.trip.count69
  br i1 %exitcond70.not, label %for.cond2.preheader, label %for.body, !llvm.loop !7

for.cond13.preheader:                             ; preds = %for.body5, %for.cond2.preheader
  %cmp1453 = icmp sgt i32 %n, 0
  br i1 %cmp1453, label %for.body16.preheader, label %for.cond24.preheader

for.body16.preheader:                             ; preds = %for.cond13.preheader
  %wide.trip.count61 = zext i32 %n to i64
  br label %for.body16

for.body5:                                        ; preds = %for.body5.preheader, %for.body5
  %indvars.iv63 = phi i64 [ 0, %for.body5.preheader ], [ %indvars.iv.next64, %for.body5 ]
  %arrayidx7 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv63
  %1 = load i32, i32* %arrayidx7, align 4, !tbaa !3
  %add8 = add nsw i32 %1, 100
  store i32 %add8, i32* %arrayidx7, align 4, !tbaa !3
  %indvars.iv.next64 = add nuw nsw i64 %indvars.iv63, 1
  %exitcond66.not = icmp eq i64 %indvars.iv.next64, %wide.trip.count65
  br i1 %exitcond66.not, label %for.cond13.preheader, label %for.body5, !llvm.loop !10

for.cond24.preheader:                             ; preds = %for.body16, %for.cond13.preheader
  %cmp2551 = icmp sgt i32 %n, 0
  br i1 %cmp2551, label %for.body27.preheader, label %for.cond.cleanup26

for.body27.preheader:                             ; preds = %for.cond24.preheader
  %wide.trip.count = zext i32 %n to i64
  br label %for.body27

for.body16:                                       ; preds = %for.body16.preheader, %for.body16
  %indvars.iv59 = phi i64 [ 0, %for.body16.preheader ], [ %indvars.iv.next60, %for.body16 ]
  %arrayidx18 = getelementptr inbounds i32, i32* %x, i64 %indvars.iv59
  %2 = load i32, i32* %arrayidx18, align 4, !tbaa !3
  %add19 = add nsw i32 %2, 100
  store i32 %add19, i32* %arrayidx18, align 4, !tbaa !3
  %indvars.iv.next60 = add nuw nsw i64 %indvars.iv59, 1
  %exitcond62.not = icmp eq i64 %indvars.iv.next60, %wide.trip.count61
  br i1 %exitcond62.not, label %for.cond24.preheader, label %for.body16, !llvm.loop !11

for.cond.cleanup26:                               ; preds = %for.body27, %for.cond24.preheader
  ret void

for.body27:                                       ; preds = %for.body27.preheader, %for.body27
  %indvars.iv = phi i64 [ 0, %for.body27.preheader ], [ %indvars.iv.next, %for.body27 ]
  %arrayidx29 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
  %3 = load i32, i32* %arrayidx29, align 4, !tbaa !3
  %add30 = add nsw i32 %3, 100
  store i32 %add30, i32* %arrayidx29, align 4, !tbaa !3
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %for.cond.cleanup26, label %for.body27, !llvm.loop !12
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
!12 = distinct !{!12, !8, !9}
