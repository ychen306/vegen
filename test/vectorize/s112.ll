; RUN: %opt -gslp %s -o %t && %check-function  2 'void s112(int, int*, int*)' 's112(1000, %%s, %%s)' %t %s

source_filename = "s112.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @s112(i32 %n, i32* noalias nocapture %a, i32* noalias nocapture readonly %b) local_unnamed_addr #0 {
entry:
  %cmp12 = icmp sgt i32 %n, 1
  br i1 %cmp12, label %for.body.preheader, label %for.cond.cleanup

for.body.preheader:                               ; preds = %entry
  %0 = add i32 %n, -2
  %1 = sext i32 %0 to i64
  br label %for.body

for.cond.cleanup.loopexit:                        ; preds = %for.body
  br label %for.cond.cleanup

for.cond.cleanup:                                 ; preds = %for.cond.cleanup.loopexit, %entry
  ret void

for.body:                                         ; preds = %for.body, %for.body.preheader
  %indvars.iv = phi i64 [ %1, %for.body.preheader ], [ %indvars.iv.next, %for.body ]
  %arrayidx = getelementptr inbounds i32, i32* %a, i64 %indvars.iv
  %2 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %arrayidx2 = getelementptr inbounds i32, i32* %b, i64 %indvars.iv
  %3 = load i32, i32* %arrayidx2, align 4, !tbaa !3
  %add = add nsw i32 %3, %2
  %4 = add nsw i64 %indvars.iv, 1
  %arrayidx5 = getelementptr inbounds i32, i32* %a, i64 %4
  store i32 %add, i32* %arrayidx5, align 4, !tbaa !3
  %indvars.iv.next = add nsw i64 %indvars.iv, -1
  %cmp = icmp sgt i64 %indvars.iv, 0
  br i1 %cmp, label %for.body, label %for.cond.cleanup.loopexit, !llvm.loop !7
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
