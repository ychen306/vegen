; RUN: %test-loop-fusion %s -do-fusion | FileCheck %s -check-prefixes=DO_FUSION
; RUN: %test-loop-fusion %s | FileCheck %s
; RUN: %test-loop-fusion %s -do-fusion > %t && %check-function  4 'int foo(int, int*, int*, int*, int*)' 'foo(512, %%s, %%s, %%s, %%s)' %t %s

; CHECK: {{[[:space:]]+}}safe

; DO_FUSION: for.body:
; DO_FUSION-NEXT:   %indvars.iv41 = phi i64 [ 0, %for.body9.preheader ], [ %indvars.iv.next42, %for.body9 ]
; DO_FUSION-NEXT:   %sx.038 = phi i32 [ 0, %for.body9.preheader ], [ %add, %for.body9 ]
; DO_FUSION-NEXT:   %indvars.iv = phi i64 [ 0, %for.body9.preheader ], [ %indvars.iv.next, %for.body9 ]
; DO_FUSION-NEXT:   %sy.035 = phi i32 [ 0, %for.body9.preheader ], [ %add12, %for.body9 ]

; DO_FUSION-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv41
; DO_FUSION-NEXT:   %t0 = load i32, i32* %arrayidx, align 4, !tbaa !3
; DO_FUSION-NEXT:   %add = add nsw i32 %t0, %sx.038
; DO_FUSION-NEXT:   %indvars.iv.next42 = add nuw nsw i64 %indvars.iv41, 1
; DO_FUSION-NEXT:   %exitcond44.not = icmp eq i64 %indvars.iv.next42, %wide.trip.count43
; DO_FUSION-NEXT:   br label %for.body9

; DO_FUSION: for.body9:
; DO_FUSION-NEXT:   %arrayidx11 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
; DO_FUSION-NEXT:   %t2 = load i32, i32* %arrayidx11, align 4, !tbaa !3
; DO_FUSION-NEXT:   %add12 = add nsw i32 %t2, %sy.035
; DO_FUSION-NEXT:   %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
; DO_FUSION-NEXT:   %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
; DO_FUSION-NEXT:   br i1 %exitcond.not, label %if.end, label %for.body{{,|$}}

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32* noalias nocapture readonly %x, i32* noalias nocapture readonly %y, i32* noalias nocapture %out1, i32* noalias nocapture %out2) local_unnamed_addr #0 {
entry:
  %cmp = icmp sgt i32 %n, 2
  br i1 %cmp, label %for.body.preheader, label %if.else

for.body.preheader:                               ; preds = %entry
  %wide.trip.count43 = zext i32 %n to i64
  br label %for.body

for.body:                                         ; preds = %for.body.preheader, %for.body
  %indvars.iv41 = phi i64 [ 0, %for.body.preheader ], [ %indvars.iv.next42, %for.body ]
  %sx.038 = phi i32 [ 0, %for.body.preheader ], [ %add, %for.body ]
  %arrayidx = getelementptr inbounds i32, i32* %x, i64 %indvars.iv41
  %t0 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %add = add nsw i32 %t0, %sx.038
  %indvars.iv.next42 = add nuw nsw i64 %indvars.iv41, 1
  %exitcond44.not = icmp eq i64 %indvars.iv.next42, %wide.trip.count43
  br i1 %exitcond44.not, label %if.end, label %for.body, !llvm.loop !7

if.else:                                          ; preds = %entry
  %t1 = load i32, i32* %x, align 4, !tbaa !3
  br label %if.end

if.end:                                           ; preds = %for.body, %if.else
  %sx.1 = phi i32 [ %t1, %if.else ], [ %add, %for.body ]
  store i32 %sx.1, i32* %out1, align 4, !tbaa !3
  br i1 %cmp, label %for.body9.preheader, label %if.else16

for.body9.preheader:                              ; preds = %if.end
  %wide.trip.count = zext i32 %n to i64
  br label %for.body9

for.body9:                                        ; preds = %for.body9.preheader, %for.body9
  %indvars.iv = phi i64 [ 0, %for.body9.preheader ], [ %indvars.iv.next, %for.body9 ]
  %sy.035 = phi i32 [ 0, %for.body9.preheader ], [ %add12, %for.body9 ]
  %arrayidx11 = getelementptr inbounds i32, i32* %y, i64 %indvars.iv
  %t2 = load i32, i32* %arrayidx11, align 4, !tbaa !3
  %add12 = add nsw i32 %t2, %sy.035
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %if.end18, label %for.body9, !llvm.loop !10

if.else16:                                        ; preds = %if.end
  %t3 = load i32, i32* %y, align 4, !tbaa !3
  br label %if.end18

if.end18:                                         ; preds = %for.body9, %if.else16
  %sy.1 = phi i32 [ %t3, %if.else16 ], [ %add12, %for.body9 ]
  store i32 %sy.1, i32* %out2, align 4, !tbaa !3
  ret void
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
