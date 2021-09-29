; RUN: %opt -gslp %s -o %t && %check-function  2 'void s118(int, int*, int*)' 's118(40, %%s, %%s)' %t %s

source_filename = "s118.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @s118(i32 %n, i32* noalias nocapture %a, i32* noalias nocapture readonly %b) local_unnamed_addr #0 {
entry:
  %0 = zext i32 %n to i64
  %cmp30 = icmp sgt i32 %n, 1
  br i1 %cmp30, label %for.cond1.preheader.preheader, label %for.cond.cleanup

for.cond1.preheader.preheader:                    ; preds = %entry
  %wide.trip.count35 = zext i32 %n to i64
  br label %for.cond1.preheader

for.cond1.preheader:                              ; preds = %for.cond.cleanup3, %for.cond1.preheader.preheader
  %indvars.iv33 = phi i64 [ 1, %for.cond1.preheader.preheader ], [ %indvars.iv.next34, %for.cond.cleanup3 ]
  %arrayidx12 = getelementptr inbounds i32, i32* %a, i64 %indvars.iv33
  br label %for.body4

for.cond.cleanup.loopexit:                        ; preds = %for.cond.cleanup3
  br label %for.cond.cleanup

for.cond.cleanup:                                 ; preds = %for.cond.cleanup.loopexit, %entry
  ret void

for.cond.cleanup3:                                ; preds = %for.body4
  %indvars.iv.next34 = add nuw nsw i64 %indvars.iv33, 1
  %exitcond36.not = icmp eq i64 %indvars.iv.next34, %wide.trip.count35
  br i1 %exitcond36.not, label %for.cond.cleanup.loopexit, label %for.cond1.preheader, !llvm.loop !3

for.body4:                                        ; preds = %for.body4, %for.cond1.preheader
  %indvars.iv = phi i64 [ 0, %for.cond1.preheader ], [ %indvars.iv.next, %for.body4 ]
  %1 = mul nuw nsw i64 %indvars.iv, %0
  %arrayidx = getelementptr inbounds i32, i32* %b, i64 %indvars.iv33
  %arrayidx6 = getelementptr inbounds i32, i32* %arrayidx, i64 %1
  %2 = load i32, i32* %arrayidx6, align 4, !tbaa !6
  %3 = xor i64 %indvars.iv, -1
  %4 = add nsw i64 %indvars.iv33, %3
  %arrayidx10 = getelementptr inbounds i32, i32* %a, i64 %4
  %5 = load i32, i32* %arrayidx10, align 4, !tbaa !6
  %mul = mul nsw i32 %5, %2
  %6 = load i32, i32* %arrayidx12, align 4, !tbaa !6
  %add = add nsw i32 %6, %mul
  store i32 %add, i32* %arrayidx12, align 4, !tbaa !6
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %indvars.iv33
  br i1 %exitcond.not, label %for.cond.cleanup3, label %for.body4, !llvm.loop !10
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
