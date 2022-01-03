; RUN: %opt -gslp -no-unroll -adce %s -o - -S | FileCheck %s

; CHECK: [[B:%.*]] = bitcast i32* %arrayidx to <2 x i32>*
; CHECK: [[LOAD:%.*]] = load <2 x i32>, <2 x i32>* [[B]]
; CHECK: [[MUL:%.*]] = mul <2 x i32> [[LOAD]], <i32 3, i32 5>
; CHECK: [[A:%.*]] = bitcast i32* %arrayidx4 to <2 x i32>*
; CHECK: store <2 x i32> [[MUL]], <2 x i32>* [[A]]

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* noalias nocapture %a, i32* noalias nocapture readonly %b) local_unnamed_addr #0 {
entry:
  %cmp34 = icmp sgt i32 %n, 0
  br i1 %cmp34, label %for.body.preheader, label %for.cond6.preheader

for.body.preheader:                               ; preds = %entry
  %wide.trip.count41 = zext i32 %n to i64
  br label %for.body

for.cond6.preheader:                              ; preds = %for.body, %entry
  %cmp732 = icmp sgt i32 %n, 0
  br i1 %cmp732, label %for.body9.preheader, label %for.cond.cleanup8

for.body9.preheader:                              ; preds = %for.cond6.preheader
  %wide.trip.count = zext i32 %n to i64
  br label %for.body9

for.body:                                         ; preds = %for.body.preheader, %for.body
  %indvars.iv38 = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next39, %for.body ]
  %0 = shl nuw nsw i64 %indvars.iv38, 1
  %arrayidx = getelementptr inbounds i32, i32* %b, i64 %0
  %1 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %mul1 = mul nsw i32 %1, 3
  %arrayidx4 = getelementptr inbounds i32, i32* %a, i64 %0
  store i32 %mul1, i32* %arrayidx4, align 4, !tbaa !3
  %indvars.iv.next39 = add nuw nsw i64 %indvars.iv38, 1
  %exitcond42.not = icmp eq i64 %indvars.iv.next39, %wide.trip.count41
  br i1 %exitcond42.not, label %for.cond6.preheader, label %for.body, !llvm.loop !7

for.cond.cleanup8:                                ; preds = %for.body9, %for.cond6.preheader
  ret void

for.body9:                                        ; preds = %for.body9.preheader, %for.body9
  %indvars.iv = phi i64 [ 0, %for.body9.preheader ], [ %indvars.iv.next, %for.body9 ]
  %2 = shl nuw nsw i64 %indvars.iv, 1
  %3 = or i64 %2, 1
  %arrayidx12 = getelementptr inbounds i32, i32* %b, i64 %3
  %4 = load i32, i32* %arrayidx12, align 4, !tbaa !3
  %mul13 = mul nsw i32 %4, 5
  %arrayidx17 = getelementptr inbounds i32, i32* %a, i64 %3
  store i32 %mul13, i32* %arrayidx17, align 4, !tbaa !3
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %for.cond.cleanup8, label %for.body9, !llvm.loop !10
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
