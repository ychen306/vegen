; RUN: %test-loop-fusion %s -do-fusion | FileCheck %s -check-prefixes=DO_FUSION
; RUN: %test-loop-fusion %s | FileCheck %s
; RUN: %test-loop-fusion %s -do-fusion > %t && %check-function  2 'int foo(int, int, int*, int*)' 'foo(64, 16, %%s, %%s)' %t %s

; CHECK: {{[[:space:]]+}}safe

; DO_FUSION: loop1.inner.body:
; DO_FUSION-NEXT:   %indvars.iv63 = phi i64 [ 0, %loop1.inner.preheader ], [ %indvars.iv.next64, %loop2.inner.body ]
; DO_FUSION-NEXT:   %indvars.iv = phi i64 [ 0, %loop1.inner.preheader ], [ %indvars.iv.next, %loop2.inner.body ]

; DO_FUSION-NEXT:   %arrayidx6 = getelementptr inbounds i32, i32* %arrayidx, i64 %indvars.iv63
; DO_FUSION-NEXT:   [[TMP1:%.*]] = load i32, i32* %arrayidx6, align 4
; DO_FUSION-NEXT:   %mul = shl nsw i32 [[TMP1]], 1
; DO_FUSION-NEXT:   store i32 %mul, i32* %arrayidx6, align 4
; DO_FUSION-NEXT:   %indvars.iv.next64 = add nuw nsw i64 %indvars.iv63, 1
; DO_FUSION-NEXT:   %exitcond66.not = icmp eq i64 %indvars.iv.next64, %wide.trip.count65
; DO_FUSION-NEXT:   br label %loop2.inner.body{{,|$}}

; DO_FUSION: loop2.inner.body:
; DO_FUSION-NEXT:   %arrayidx23 = getelementptr inbounds i32, i32* %arrayidx21, i64 %indvars.iv
; DO_FUSION-NEXT:   [[TMP2:%.*]] = load i32, i32* %arrayidx23, align 4
; DO_FUSION-NEXT:   %mul24 = shl nsw i32 [[TMP2:%.*]], 1
; DO_FUSION-NEXT:   store i32 %mul24, i32* %arrayidx23, align 4
; DO_FUSION-NEXT:   %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
; DO_FUSION-NEXT:   %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
; DO_FUSION-NEXT:   br i1 %exitcond.not, label %loop1.inner.exit, label %loop1.inner.body

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32 %m, i32* noalias nocapture %x, i32* noalias nocapture %y) local_unnamed_addr #0 {
entry:
  %0 = zext i32 %m to i64
  %cmp56 = icmp sgt i32 %n, 0
  br i1 %cmp56, label %loop1.outer.preheader, label %loop2.outer.guard

loop1.outer.preheader:
  %cmp254 = icmp sgt i32 %m, 0
  %wide.trip.count69 = zext i32 %n to i64
  br label %loop1.inner.guard

loop1.inner.guard:
  %indvars.iv67 = phi i64 [ 0, %loop1.outer.preheader ], [ %indvars.iv.next68, %loop1.inner.exit ]
  br i1 %cmp254, label %loop1.inner.preheader, label %loop1.inner.exit

loop1.inner.preheader:
  %1 = mul nuw nsw i64 %indvars.iv67, %0
  %arrayidx = getelementptr inbounds i32, i32* %x, i64 %1
  %wide.trip.count65 = zext i32 %m to i64
  br label %loop1.inner.body

loop2.outer.guard:
  %cmp1251 = icmp sgt i32 %n, 0
  br i1 %cmp1251, label %loop2.outer.preheader, label %exit

loop2.outer.preheader:
  %cmp1749 = icmp sgt i32 %m, 0
  %wide.trip.count61 = zext i32 %n to i64
  br label %loop2.inner.guard

loop1.inner.exit:
  %indvars.iv.next68 = add nuw nsw i64 %indvars.iv67, 1
  %exitcond70.not = icmp eq i64 %indvars.iv.next68, %wide.trip.count69
  br i1 %exitcond70.not, label %loop2.outer.guard, label %loop1.inner.guard, !llvm.loop !3

loop1.inner.body:
  %indvars.iv63 = phi i64 [ 0, %loop1.inner.preheader ], [ %indvars.iv.next64, %loop1.inner.body ]
  %arrayidx6 = getelementptr inbounds i32, i32* %arrayidx, i64 %indvars.iv63
  %2 = load i32, i32* %arrayidx6, align 4, !tbaa !6
  %mul = shl nsw i32 %2, 1
  store i32 %mul, i32* %arrayidx6, align 4, !tbaa !6
  %indvars.iv.next64 = add nuw nsw i64 %indvars.iv63, 1
  %exitcond66.not = icmp eq i64 %indvars.iv.next64, %wide.trip.count65
  br i1 %exitcond66.not, label %loop1.inner.exit, label %loop1.inner.body, !llvm.loop !10

loop2.inner.guard: %indvars.iv59 = phi i64 [ 0, %loop2.outer.preheader ], [ %indvars.iv.next60, %loop2.inner.exit ]
  br i1 %cmp1749, label %loop2.inner.preheader, label %loop2.inner.exit

loop2.inner.preheader:
  %3 = mul nuw nsw i64 %indvars.iv59, %0
  %arrayidx21 = getelementptr inbounds i32, i32* %y, i64 %3
  %wide.trip.count = zext i32 %m to i64
  br label %loop2.inner.body

exit:
  ret void

loop2.inner.exit:
  %indvars.iv.next60 = add nuw nsw i64 %indvars.iv59, 1
  %exitcond62.not = icmp eq i64 %indvars.iv.next60, %wide.trip.count61
  br i1 %exitcond62.not, label %exit, label %loop2.inner.guard, !llvm.loop !11

loop2.inner.body:
  %indvars.iv = phi i64 [ 0, %loop2.inner.preheader ], [ %indvars.iv.next, %loop2.inner.body ]
  %arrayidx23 = getelementptr inbounds i32, i32* %arrayidx21, i64 %indvars.iv
  %4 = load i32, i32* %arrayidx23, align 4, !tbaa !6
  %mul24 = shl nsw i32 %4, 1
  store i32 %mul24, i32* %arrayidx23, align 4, !tbaa !6
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %loop2.inner.exit, label %loop2.inner.body, !llvm.loop !12
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = distinct !{!3, !4, !5}
!4 = !{!"llvm.loop.mustprogress"}
!5 = !{!"llvm.loop.unroll.disable"}
!6 = !{!7, !7, i64 0}
!7 = !{!"int", !8, i64 0}
!8 = !{!"omnipotent char", !9, i64 0}
!9 = !{!"Simple C/C++ TBAA"}
!10 = distinct !{!10, !4, !5}
!11 = distinct !{!11, !4, !5}
!12 = distinct !{!12, !4, !5}
