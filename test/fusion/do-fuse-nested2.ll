; RUN: %test-loop-fusion %s -do-fusion | FileCheck %s -check-prefixes=DO_FUSION
; RUN: %test-loop-fusion %s | FileCheck %s
; RUN: %test-loop-fusion %s -do-fusion > %t && %check-function  2 'int foo(int, int, int, int*, int*)' 'foo(64, 8, 2, %%s, %%s)' %t %s

; CHECK: {{[[:space:]]+}}safe

; DO_FUSION: for.body8:
; DO_FUSION-NEXT:   %indvars.iv101 = phi i64 [ 0, %for.body8.lr.ph ], [ %indvars.iv.next102, %for.body33 ]
; DO_FUSION-NEXT:   %indvars.iv = phi i64 [ 0, %for.body8.lr.ph ], [ %indvars.iv.next, %for.body33 ]
; DO_FUSION-NEXT:   %arrayidx12 = getelementptr inbounds i32, i32* %arrayidx10, i64 %indvars.iv101
; DO_FUSION-NEXT:   [[TMP1:%.*]] = load i32, i32* %arrayidx12, align 4
; DO_FUSION-NEXT:   %mul = mul nsw i32 [[TMP1]], 42
; DO_FUSION-NEXT:   store i32 %mul, i32* %arrayidx12, align 4
; DO_FUSION-NEXT:   %indvars.iv.next102 = add nuw nsw i64 %indvars.iv101, 1
; DO_FUSION-NEXT:   %exitcond104.not = icmp eq i64 %indvars.iv.next102, %wide.trip.count103
; DO_FUSION-NEXT:   br label %for.body33

; DO_FUSION: for.body33:
; DO_FUSION-NEXT:   %arrayidx39 = getelementptr inbounds i32, i32* %arrayidx37, i64 %indvars.iv
; DO_FUSION-NEXT:   [[TMP2:%.*]] = load i32, i32* %arrayidx39, align 4
; DO_FUSION-NEXT:   %mul40 = mul nsw i32 [[TMP2]], 42
; DO_FUSION-NEXT:   store i32 %mul40, i32* %arrayidx39, align 4
; DO_FUSION-NEXT:   %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
; DO_FUSION-NEXT:   %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
; DO_FUSION-NEXT:   br i1 %exitcond.not, label %for.cond.cleanup7, label %for.body8

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, i32 %m, i32 %l, i32* nocapture %x, i32* nocapture %y) local_unnamed_addr #0 {
entry:
  %0 = zext i32 %m to i64
  %1 = zext i32 %l to i64
  %cmp90 = icmp sgt i32 %n, 0
  br i1 %cmp90, label %for.cond1.preheader.lr.ph, label %for.cond20.preheader

for.cond1.preheader.lr.ph:                        ; preds = %entry
  %cmp287 = icmp sgt i32 %m, 0
  %cmp685 = icmp sgt i32 %l, 0
  %2 = mul nuw i64 %1, %0
  %wide.trip.count111 = zext i32 %n to i64
  br label %for.cond1.preheader

for.cond1.preheader:                              ; preds = %for.cond1.preheader.lr.ph, %for.cond.cleanup3
  %indvars.iv109 = phi i64 [ 0, %for.cond1.preheader.lr.ph ], [ %indvars.iv.next110, %for.cond.cleanup3 ]
  br i1 %cmp287, label %for.cond5.preheader.lr.ph, label %for.cond.cleanup3

for.cond5.preheader.lr.ph:                        ; preds = %for.cond1.preheader
  %3 = mul nsw i64 %2, %indvars.iv109
  %arrayidx = getelementptr inbounds i32, i32* %x, i64 %3
  %wide.trip.count107 = zext i32 %m to i64
  br label %for.cond5.preheader

for.cond20.preheader:                             ; preds = %for.cond.cleanup3, %entry
  %cmp2182 = icmp sgt i32 %n, 0
  br i1 %cmp2182, label %for.cond25.preheader.lr.ph, label %for.cond.cleanup22

for.cond25.preheader.lr.ph:                       ; preds = %for.cond20.preheader
  %cmp2679 = icmp sgt i32 %m, 0
  %cmp3177 = icmp sgt i32 %l, 0
  %4 = mul nuw i64 %1, %0
  %wide.trip.count99 = zext i32 %n to i64
  br label %for.cond25.preheader

for.cond5.preheader:                              ; preds = %for.cond5.preheader.lr.ph, %for.cond.cleanup7
  %indvars.iv105 = phi i64 [ 0, %for.cond5.preheader.lr.ph ], [ %indvars.iv.next106, %for.cond.cleanup7 ]
  br i1 %cmp685, label %for.body8.lr.ph, label %for.cond.cleanup7

for.body8.lr.ph:                                  ; preds = %for.cond5.preheader
  %5 = mul nuw nsw i64 %indvars.iv105, %1
  %arrayidx10 = getelementptr inbounds i32, i32* %arrayidx, i64 %5
  %wide.trip.count103 = zext i32 %l to i64
  br label %for.body8

for.cond.cleanup3:                                ; preds = %for.cond.cleanup7, %for.cond1.preheader
  %indvars.iv.next110 = add nuw nsw i64 %indvars.iv109, 1
  %exitcond112.not = icmp eq i64 %indvars.iv.next110, %wide.trip.count111
  br i1 %exitcond112.not, label %for.cond20.preheader, label %for.cond1.preheader, !llvm.loop !3

for.cond.cleanup7:                                ; preds = %for.body8, %for.cond5.preheader
  %indvars.iv.next106 = add nuw nsw i64 %indvars.iv105, 1
  %exitcond108.not = icmp eq i64 %indvars.iv.next106, %wide.trip.count107
  br i1 %exitcond108.not, label %for.cond.cleanup3, label %for.cond5.preheader, !llvm.loop !6

for.body8:                                        ; preds = %for.body8.lr.ph, %for.body8
  %indvars.iv101 = phi i64 [ 0, %for.body8.lr.ph ], [ %indvars.iv.next102, %for.body8 ]
  %arrayidx12 = getelementptr inbounds i32, i32* %arrayidx10, i64 %indvars.iv101
  %6 = load i32, i32* %arrayidx12, align 4, !tbaa !7
  %mul = mul nsw i32 %6, 42
  store i32 %mul, i32* %arrayidx12, align 4, !tbaa !7
  %indvars.iv.next102 = add nuw nsw i64 %indvars.iv101, 1
  %exitcond104.not = icmp eq i64 %indvars.iv.next102, %wide.trip.count103
  br i1 %exitcond104.not, label %for.cond.cleanup7, label %for.body8, !llvm.loop !11

for.cond25.preheader:                             ; preds = %for.cond25.preheader.lr.ph, %for.cond.cleanup27
  %indvars.iv97 = phi i64 [ 0, %for.cond25.preheader.lr.ph ], [ %indvars.iv.next98, %for.cond.cleanup27 ]
  br i1 %cmp2679, label %for.cond30.preheader.lr.ph, label %for.cond.cleanup27

for.cond30.preheader.lr.ph:                       ; preds = %for.cond25.preheader
  %7 = mul nsw i64 %4, %indvars.iv97
  %arrayidx35 = getelementptr inbounds i32, i32* %y, i64 %7
  %wide.trip.count95 = zext i32 %m to i64
  br label %for.cond30.preheader

for.cond.cleanup22:                               ; preds = %for.cond.cleanup27, %for.cond20.preheader
  ret void

for.cond30.preheader:                             ; preds = %for.cond30.preheader.lr.ph, %for.cond.cleanup32
  %indvars.iv93 = phi i64 [ 0, %for.cond30.preheader.lr.ph ], [ %indvars.iv.next94, %for.cond.cleanup32 ]
  br i1 %cmp3177, label %for.body33.lr.ph, label %for.cond.cleanup32

for.body33.lr.ph:                                 ; preds = %for.cond30.preheader
  %8 = mul nuw nsw i64 %indvars.iv93, %1
  %arrayidx37 = getelementptr inbounds i32, i32* %arrayidx35, i64 %8
  %wide.trip.count = zext i32 %l to i64
  br label %for.body33

for.cond.cleanup27:                               ; preds = %for.cond.cleanup32, %for.cond25.preheader
  %indvars.iv.next98 = add nuw nsw i64 %indvars.iv97, 1
  %exitcond100.not = icmp eq i64 %indvars.iv.next98, %wide.trip.count99
  br i1 %exitcond100.not, label %for.cond.cleanup22, label %for.cond25.preheader, !llvm.loop !12

for.cond.cleanup32:                               ; preds = %for.body33, %for.cond30.preheader
  %indvars.iv.next94 = add nuw nsw i64 %indvars.iv93, 1
  %exitcond96.not = icmp eq i64 %indvars.iv.next94, %wide.trip.count95
  br i1 %exitcond96.not, label %for.cond.cleanup27, label %for.cond30.preheader, !llvm.loop !13

for.body33:                                       ; preds = %for.body33.lr.ph, %for.body33
  %indvars.iv = phi i64 [ 0, %for.body33.lr.ph ], [ %indvars.iv.next, %for.body33 ]
  %arrayidx39 = getelementptr inbounds i32, i32* %arrayidx37, i64 %indvars.iv
  %9 = load i32, i32* %arrayidx39, align 4, !tbaa !7
  %mul40 = mul nsw i32 %9, 42
  store i32 %mul40, i32* %arrayidx39, align 4, !tbaa !7
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %for.cond.cleanup32, label %for.body33, !llvm.loop !14
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
!6 = distinct !{!6, !4, !5}
!7 = !{!8, !8, i64 0}
!8 = !{!"int", !9, i64 0}
!9 = !{!"omnipotent char", !10, i64 0}
!10 = !{!"Simple C/C++ TBAA"}
!11 = distinct !{!11, !4, !5}
!12 = distinct !{!12, !4, !5}
!13 = distinct !{!13, !4, !5}
!14 = distinct !{!14, !4, !5}
