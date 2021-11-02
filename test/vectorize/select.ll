; RUN: %opt -gslp -no-unroll %s -S | FileCheck %s

source_filename = "select.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; CHECK:   [[X_ADDR:%.*]] = bitcast i32* %x to <4 x i32>*
; CHECK-NEXT:  [[X:%.*]] = load <4 x i32>, <4 x i32>* [[X_ADDR]]
; CHECK-NEXT:   [[Y_ADDR:%.*]] = bitcast i32* %y to <4 x i32>*
; CHECK-NEXT:  [[Y:%.*]] = load <4 x i32>, <4 x i32>* [[Y_ADDR]]
; CHECK-NEXT:   [[C_ADDR:%.*]] = bitcast i32* %c to <4 x i32>*
; CHECK-NEXT:  [[C:%.*]] = load <4 x i32>, <4 x i32>* [[C_ADDR]]
; CHECK-NEXT:  [[CMP:%.*]] = icmp eq <4 x i32> [[C]], zeroinitializer
; CHECK-NEXT:  [[SELECT:%.*]] = select <4 x i1> [[CMP]], <4 x i32> [[Y]], <4 x i32> [[X]]
; CHECK-NEXT:  [[OUT:%.*]] = bitcast i32* %out to <4 x i32>*
; CHECK-NEXT:  store <4 x i32> [[SELECT]], <4 x i32>* [[OUT]]

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @select(i32* noalias nocapture readonly %c, i32* noalias nocapture readonly %x, i32* noalias nocapture readonly %y, i32* noalias nocapture %out) local_unnamed_addr #0 {
entry:
  %0 = load i32, i32* %x, align 4, !tbaa !3
  %1 = load i32, i32* %y, align 4, !tbaa !3
  %2 = load i32, i32* %c, align 4, !tbaa !3
  %tobool.not = icmp eq i32 %2, 0
  %cond = select i1 %tobool.not, i32 %1, i32 %0
  store i32 %cond, i32* %out, align 4, !tbaa !3
  %arrayidx.1 = getelementptr inbounds i32, i32* %x, i64 1
  %3 = load i32, i32* %arrayidx.1, align 4, !tbaa !3
  %arrayidx2.1 = getelementptr inbounds i32, i32* %y, i64 1
  %4 = load i32, i32* %arrayidx2.1, align 4, !tbaa !3
  %arrayidx4.1 = getelementptr inbounds i32, i32* %c, i64 1
  %5 = load i32, i32* %arrayidx4.1, align 4, !tbaa !3
  %tobool.not.1 = icmp eq i32 %5, 0
  %cond.1 = select i1 %tobool.not.1, i32 %4, i32 %3
  %arrayidx6.1 = getelementptr inbounds i32, i32* %out, i64 1
  store i32 %cond.1, i32* %arrayidx6.1, align 4, !tbaa !3
  %arrayidx.2 = getelementptr inbounds i32, i32* %x, i64 2
  %6 = load i32, i32* %arrayidx.2, align 4, !tbaa !3
  %arrayidx2.2 = getelementptr inbounds i32, i32* %y, i64 2
  %7 = load i32, i32* %arrayidx2.2, align 4, !tbaa !3
  %arrayidx4.2 = getelementptr inbounds i32, i32* %c, i64 2
  %8 = load i32, i32* %arrayidx4.2, align 4, !tbaa !3
  %tobool.not.2 = icmp eq i32 %8, 0
  %cond.2 = select i1 %tobool.not.2, i32 %7, i32 %6
  %arrayidx6.2 = getelementptr inbounds i32, i32* %out, i64 2
  store i32 %cond.2, i32* %arrayidx6.2, align 4, !tbaa !3
  %arrayidx.3 = getelementptr inbounds i32, i32* %x, i64 3
  %9 = load i32, i32* %arrayidx.3, align 4, !tbaa !3
  %arrayidx2.3 = getelementptr inbounds i32, i32* %y, i64 3
  %10 = load i32, i32* %arrayidx2.3, align 4, !tbaa !3
  %arrayidx4.3 = getelementptr inbounds i32, i32* %c, i64 3
  %11 = load i32, i32* %arrayidx4.3, align 4, !tbaa !3
  %tobool.not.3 = icmp eq i32 %11, 0
  %cond.3 = select i1 %tobool.not.3, i32 %10, i32 %9
  %arrayidx6.3 = getelementptr inbounds i32, i32* %out, i64 3
  store i32 %cond.3, i32* %arrayidx6.3, align 4, !tbaa !3
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
