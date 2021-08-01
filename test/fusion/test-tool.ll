; This is to test do-fusion's `-fusion-group` option

; RUN: %test-loop-fusion %s -do-fusion -fusion-group=for.body,for.body5 | FileCheck %s -check-prefixes=DO_FUSION
; RUN: %test-loop-fusion %s -fusion-group=for.body,for.body5 | FileCheck %s
; RUN: %test-loop-fusion %s -do-fusion > %t && %check-function  4 'int foo(int, int*, int*, int*, int*)' 'foo(512, %%s, %%s, %%s, %%s)' %t %s

; CHECK: {{[[:space:]]+}}safe

; DO_FUSION: for.body:
; DO_FUSION-NEXT:   %indvars.iv25 = phi i64 [ 0, %for.body5.preheader ], [ %indvars.iv.next26, %for.body5 ]
; DO_FUSION-NEXT:   %s.023 = phi i32 [ 0, %for.body5.preheader ], [ %add, %for.body5 ]
; DO_FUSION-NEXT:   %indvars.iv = phi i64 [ 0, %for.body5.preheader ], [ %indvars.iv.next, %for.body5 ]

; DO_FUSION-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv25
; DO_FUSION-NEXT:   %1 = load i32, i32* %arrayidx, align 4
; DO_FUSION-NEXT:   %add = add nsw i32 %1, %s.023
; DO_FUSION-NEXT:   %indvars.iv.next26 = add nuw nsw i64 %indvars.iv25, 1
; DO_FUSION-NEXT:   %exitcond28.not = icmp eq i64 %indvars.iv.next26, %wide.trip.count27
; DO_FUSION-NEXT:   br label %for.body5

; DO_FUSION: for.body5:
; DO_FUSION-NEXT:   %arrayidx7 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
; DO_FUSION-NEXT:   %2 = load i32, i32* %arrayidx7, align 4
; DO_FUSION-NEXT:   %mul = mul nsw i32 %2, %0
; DO_FUSION-NEXT:   store i32 %mul, i32* %arrayidx7, align 4
; DO_FUSION-NEXT:   %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
; DO_FUSION-NEXT:   %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
; DO_FUSION-NEXT:   br i1 %exitcond.not, label %for.cond.cleanup, label %for.body{{,|$}}


; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* noalias nocapture readonly %x, i32* noalias nocapture %y, i32* noalias nocapture %t1, i32* noalias nocapture readonly %t2) local_unnamed_addr #0 {
entry:
  %cmp22 = icmp sgt i32 %n, 0
  br i1 %cmp22, label %for.body.preheader, label %for.cond.cleanup

for.body.preheader:                               ; preds = %entry
  %wide.trip.count27 = zext i32 %n to i64
  br label %for.body

for.cond.cleanup:                                 ; preds = %for.body, %entry
  %s.0.lcssa = phi i32 [ 0, %entry ], [ %add, %for.body ]
  store i32 %s.0.lcssa, i32* %t1, align 4, !tbaa !3
  %cmp320 = icmp sgt i32 %n, 0
  br i1 %cmp320, label %inbetween, label %for.cond.cleanup4

inbetween:
  %load = load i32, i32* %t2, align 4, !tbaa !3
  %0 = add i32 %load, 42
  br label %for.body5.preheader

for.body5.preheader:                                  ; preds = %for.cond.cleanup
  %wide.trip.count = zext i32 %n to i64
  br label %for.body5

for.body:                                         ; preds = %for.body.preheader, %for.body
  %indvars.iv25 = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next26, %for.body ]
  %s.023 = phi i32 [ 0, %for.body.preheader ], [ %add, %for.body ]
  %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv25
  %1 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %add = add nsw i32 %1, %s.023
  %indvars.iv.next26 = add nuw nsw i64 %indvars.iv25, 1
  %exitcond28.not = icmp eq i64 %indvars.iv.next26, %wide.trip.count27
  br i1 %exitcond28.not, label %for.cond.cleanup, label %for.body, !llvm.loop !7

for.cond.cleanup4:                                ; preds = %for.body5, %for.cond.cleanup
  ret void

for.body5:                                        ; preds = %for.body5.preheader, %for.body5
  %indvars.iv = phi i64 [ 0, %for.body5.preheader ], [ %indvars.iv.next, %for.body5 ]
  %arrayidx7 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
  %2 = load i32, i32* %arrayidx7, align 4, !tbaa !3
  %mul = mul nsw i32 %2, %0
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
