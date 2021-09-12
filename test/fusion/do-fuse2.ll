; RUN: %test-loop-fusion %s -do-fusion | FileCheck %s -check-prefixes=DO_FUSION
; RUN: %test-loop-fusion %s | FileCheck %s
; RUN: %test-loop-fusion %s -do-fusion > %t && %check-function  4 'int foo(int, int*, int*, int*, int*)' 'foo(512, %%s, %%s, %%s, %%s)' %t %s

; CHECK: {{[[:space:]]+}}safe

; DO_FUSION: for.body:
; DO_FUSION-NEXT:   %indvars.iv30 = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next31, %for.body5 ]
; DO_FUSION-NEXT:   %sx.027 = phi i32 [ 0, %for.body.preheader ], [ %add, %for.body5 ]
; DO_FUSION-NEXT:   %indvars.iv = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next, %for.body5 ]
; DO_FUSION-NEXT:   %sy.024 = phi i32 [ 0, %for.body.preheader ], [ %add8, %for.body5 ]

; DO_FUSION-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv30
; DO_FUSION-NEXT:   %t0 = load i32, i32* %arrayidx, align 4, !tbaa !3
; DO_FUSION-NEXT:   %add = add nsw i32 %t0, %sx.027
; DO_FUSION-NEXT:   %indvars.iv.next31 = add nuw nsw i64 %indvars.iv30, 1
; DO_FUSION-NEXT:   %exitcond33.not = icmp eq i64 %indvars.iv.next31, %wide.trip.count32
; DO_FUSION-NEXT:   br label %for.body5

; DO_FUSION: for.body5:
; DO_FUSION-NEXT:   %arrayidx7 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
; DO_FUSION-NEXT:   %t1 = load i32, i32* %arrayidx7, align 4, !tbaa !3
; DO_FUSION-NEXT:   %add8 = add nsw i32 %t1, %sy.024
; DO_FUSION-NEXT:   %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
; DO_FUSION-NEXT:   %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
; DO_FUSION-NEXT:   br i1 %exitcond.not, label %for.cond2.preheader, label %for.body{{,|$}}

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* nocapture readonly %x, i32* nocapture readonly %y, i32* nocapture %out, i32* nocapture %out2) local_unnamed_addr #0 {
entry:
  %cmp26 = icmp sgt i32 %n, 0
  br i1 %cmp26, label %for.body.preheader, label %for.cond2.preheader

for.body.preheader:                               ; preds = %entry
  %wide.trip.count32 = zext i32 %n to i64
  br label %for.body

for.cond2.preheader:                              ; preds = %for.body, %entry
  %sx.0.lcssa = phi i32 [ 0, %entry ], [ %add, %for.body ]
  %cmp323 = icmp sgt i32 %n, 0
  br i1 %cmp323, label %for.body5.preheader, label %for.cond.cleanup4

for.body5.preheader:                              ; preds = %for.cond2.preheader
  %wide.trip.count = zext i32 %n to i64
  br label %for.body5

for.body:                                         ; preds = %for.body.preheader, %for.body
  %indvars.iv30 = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next31, %for.body ]
  %sx.027 = phi i32 [ 0, %for.body.preheader ], [ %add, %for.body ]
  %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv30
  %t0 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %add = add nsw i32 %t0, %sx.027
  %indvars.iv.next31 = add nuw nsw i64 %indvars.iv30, 1
  %exitcond33.not = icmp eq i64 %indvars.iv.next31, %wide.trip.count32
  br i1 %exitcond33.not, label %for.cond2.preheader, label %for.body, !llvm.loop !7

for.cond.cleanup4:                                ; preds = %for.body5, %for.cond2.preheader
  %sy.0.lcssa = phi i32 [ 0, %for.cond2.preheader ], [ %add8, %for.body5 ]
  store i32 %sx.0.lcssa, i32* %out, align 4, !tbaa !3
  store i32 %sy.0.lcssa, i32* %out2, align 4, !tbaa !3
  ret void

for.body5:                                        ; preds = %for.body5.preheader, %for.body5
  %indvars.iv = phi i64 [ 0, %for.body5.preheader ], [ %indvars.iv.next, %for.body5 ]
  %sy.024 = phi i32 [ 0, %for.body5.preheader ], [ %add8, %for.body5 ]
  %arrayidx7 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
  %t1 = load i32, i32* %arrayidx7, align 4, !tbaa !3
  %add8 = add nsw i32 %t1, %sy.024
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
