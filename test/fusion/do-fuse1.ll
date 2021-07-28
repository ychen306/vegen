; RUN: %test-loop-fusion %s -do-fusion | FileCheck %s -check-prefixes=DO_FUSION
; RUN: %test-loop-fusion %s | FileCheck %s

; CHECK: {{[[:space:]]+}}safe

; DO_FUSION: for.body.preheader:
; DO_FUSION-NEXT:   %wide.trip.count25 = zext i32 %n to i64
; DO_FUSION-NEXT:   br label %for.body5.preheader

; DO_FUSION: for.cond2.preheader:
; DO_FUSION-NEXT:  %cmp319 = icmp sgt i32 %n, 0
; DO_FUSION-NEXT:  br i1 %cmp319, label %for.cond.cleanup4, label %for.cond.cleanup4

; DO_FUSION: for.body5.preheader
; DO_FUSION-NEXT:   %wide.trip.count = zext i32 %n to i64
; DO_FUSION-NEXT:   br label %for.body{{$}}

; DO_FUSION: for.body:
; DO_FUSION-NEXT:   %indvars.iv23 = phi i64 [ 0, %for.body5.preheader ], [ %indvars.iv.next24, %for.body5 ]
; DO_FUSION-NEXT:   %indvars.iv = phi i64 [ 0, %for.body5.preheader ], [ %indvars.iv.next, %for.body5 ]

; DO_FUSION-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv23
; DO_FUSION-NEXT:   %t0 = load i32, i32* %arrayidx, align 4
; DO_FUSION-NEXT:   %mul = shl nsw i32 %t0, 1
; DO_FUSION-NEXT:   store i32 %mul, i32* %arrayidx, align 4
; DO_FUSION-NEXT:   %indvars.iv.next24 = add nuw nsw i64 %indvars.iv23, 1
; DO_FUSION-NEXT:   %exitcond26.not = icmp eq i64 %indvars.iv.next24, %wide.trip.count25
; DO_FUSION-NEXT:   br label %for.body5

; DO_FUSION: for.body5:
; DO_FUSION-NEXT:   %arrayidx7 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
; DO_FUSION-NEXT:   %t1 = load i32, i32* %arrayidx7, align 4
; DO_FUSION-NEXT:   %mul8 = shl nsw i32 %t1, 1
; DO_FUSION-NEXT:   store i32 %mul8, i32* %arrayidx7, align 4
; DO_FUSION-NEXT:   %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
; DO_FUSION-NEXT:   %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
; DO_FUSION-NEXT:   br i1 %exitcond.not, label %for.cond2.preheader, label %for.body{{$}}


; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* noalias nocapture %x, i32* noalias nocapture %y) local_unnamed_addr #0 {
entry:
  %cmp21 = icmp sgt i32 %n, 0
  br i1 %cmp21, label %for.body.preheader, label %for.cond2.preheader

for.body.preheader:                               ; preds = %entry
  %wide.trip.count25 = zext i32 %n to i64
  br label %for.body

for.cond2.preheader:                              ; preds = %for.body, %entry
  %cmp319 = icmp sgt i32 %n, 0
  br i1 %cmp319, label %for.body5.preheader, label %for.cond.cleanup4

for.body5.preheader:                              ; preds = %for.cond2.preheader
  %wide.trip.count = zext i32 %n to i64
  br label %for.body5

for.body:                                         ; preds = %for.body.preheader, %for.body
  %indvars.iv23 = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next24, %for.body ]
  %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv23
  %t0 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %mul = shl nsw i32 %t0, 1
  store i32 %mul, i32* %arrayidx, align 4, !tbaa !3
  %indvars.iv.next24 = add nuw nsw i64 %indvars.iv23, 1
  %exitcond26.not = icmp eq i64 %indvars.iv.next24, %wide.trip.count25
  br i1 %exitcond26.not, label %for.cond2.preheader, label %for.body

for.cond.cleanup4:                                ; preds = %for.body5, %for.cond2.preheader
  ret void

for.body5:                                        ; preds = %for.body5.preheader, %for.body5
  %indvars.iv = phi i64 [ 0, %for.body5.preheader ], [ %indvars.iv.next, %for.body5 ]
  %arrayidx7 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
  %t1 = load i32, i32* %arrayidx7, align 4, !tbaa !3
  %mul8 = shl nsw i32 %t1, 1
  store i32 %mul8, i32* %arrayidx7, align 4, !tbaa !3
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %for.cond.cleanup4, label %for.body5
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
