; RUN: %opt -gslp %s -o - -S | FileCheck %s

; CHECK: for.body.lr.ph:
; CHECK-NEXT:   %0 = bitcast i32* %s to <2 x i32>*
; CHECK-NEXT:   %1 = load <2 x i32>, <2 x i32>* %0, align 4
; CHECK-NEXT:   %2 = sext i32 %n to i64
; CHECK-NEXT:   br label %for.body

; CHECK: for.cond.for.cond.cleanup_crit_edge:
; CHECK-NEXT:   %3 = bitcast i32* %s to <2 x i32>*
; CHECK-NEXT:   store <2 x i32> %8, <2 x i32>* %3, align 4, !tbaa !3
; CHECK-NEXT:   br label %for.cond.cleanup

; CHECK: for.body:
; CHECK-NEXT:   %4 = phi <2 x i32> [ %1, %for.body.lr.ph ], [ %8, %for.body ]

; CHECK:   %6 = bitcast i32* %arrayidx to <2 x i32>*
; CHECK-NEXT:   %7 = load <2 x i32>, <2 x i32>* %6, align 4, !tbaa !3
; CHECK-NEXT:   %8 = add <2 x i32> %4, %7

target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* noalias nocapture readonly %a, i32* noalias nocapture %s) local_unnamed_addr #0 {
entry:
  %cmp14 = icmp sgt i32 %n, 0
  br i1 %cmp14, label %for.body.lr.ph, label %for.cond.cleanup

for.body.lr.ph:                                   ; preds = %entry
  %arrayidx5 = getelementptr inbounds i32, i32* %s, i64 1
  %s.promoted = load i32, i32* %s, align 4, !tbaa !3
  %arrayidx5.promoted = load i32, i32* %arrayidx5, align 4, !tbaa !3
  %0 = sext i32 %n to i64
  br label %for.body

for.cond.for.cond.cleanup_crit_edge:              ; preds = %for.body
  store i32 %add, i32* %s, align 4, !tbaa !3
  store i32 %add6, i32* %arrayidx5, align 4, !tbaa !3
  br label %for.cond.cleanup

for.cond.cleanup:                                 ; preds = %for.cond.for.cond.cleanup_crit_edge, %entry
  ret void

for.body:                                         ; preds = %for.body.lr.ph, %for.body
  %indvars.iv = phi i64 [ 0, %for.body.lr.ph ], [ %indvars.iv.next, %for.body ]
  %add616 = phi i32 [ %arrayidx5.promoted, %for.body.lr.ph ], [ %add6, %for.body ]
  %1 = phi i32 [ %s.promoted, %for.body.lr.ph ], [ %add, %for.body ]
  %arrayidx = getelementptr inbounds i32, i32* %a, i64 %indvars.iv
  %2 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %add = add nsw i32 %1, %2
  %3 = or i64 %indvars.iv, 1
  %arrayidx4 = getelementptr inbounds i32, i32* %a, i64 %3
  %4 = load i32, i32* %arrayidx4, align 4, !tbaa !3
  %add6 = add nsw i32 %add616, %4
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 2
  %cmp = icmp slt i64 %indvars.iv.next, %0
  br i1 %cmp, label %for.body, label %for.cond.for.cond.cleanup_crit_edge, !llvm.loop !7
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
