; RUN: %opt -gslp %s

source_filename = "t.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %x, float* noalias nocapture readonly %a, float* noalias nocapture readonly %b, float* noalias nocapture %c) local_unnamed_addr #0 {
entry:
  %tobool.not = icmp eq i32 %x, 0
  br i1 %tobool.not, label %for.inc.3, label %if.then

if.then:                                          ; preds = %entry
  %0 = load float, float* %a, align 4, !tbaa !3
  %1 = load float, float* %b, align 4, !tbaa !3
  %cmp3 = fcmp olt float %0, %1
  br i1 %cmp3, label %if.then4, label %for.inc

if.then4:                                         ; preds = %if.then
  store float %0, float* %c, align 4, !tbaa !3
  br label %for.inc

for.inc:                                          ; preds = %if.then4, %if.then
  br i1 %tobool.not, label %for.inc.3, label %if.then.1

if.then.1:                                        ; preds = %for.inc
  %arrayidx.1 = getelementptr inbounds float, float* %a, i64 1
  %2 = load float, float* %arrayidx.1, align 4, !tbaa !3
  %arrayidx2.1 = getelementptr inbounds float, float* %b, i64 1
  %3 = load float, float* %arrayidx2.1, align 4, !tbaa !3
  %cmp3.1 = fcmp olt float %2, %3
  br i1 %cmp3.1, label %if.then4.1, label %for.inc.1

if.then4.1:                                       ; preds = %if.then.1
  %arrayidx8.1 = getelementptr inbounds float, float* %c, i64 1
  store float %2, float* %arrayidx8.1, align 4, !tbaa !3
  br label %for.inc.1

for.inc.1:                                        ; preds = %if.then4.1, %if.then.1
  br i1 %tobool.not, label %for.inc.3, label %if.then.2

if.then.2:                                        ; preds = %for.inc.1
  %arrayidx.2 = getelementptr inbounds float, float* %a, i64 2
  %4 = load float, float* %arrayidx.2, align 4, !tbaa !3
  %arrayidx2.2 = getelementptr inbounds float, float* %b, i64 2
  %5 = load float, float* %arrayidx2.2, align 4, !tbaa !3
  %cmp3.2 = fcmp olt float %4, %5
  br i1 %cmp3.2, label %if.then4.2, label %for.inc.2

if.then4.2:                                       ; preds = %if.then.2
  %arrayidx8.2 = getelementptr inbounds float, float* %c, i64 2
  store float %4, float* %arrayidx8.2, align 4, !tbaa !3
  br label %for.inc.2

for.inc.2:                                        ; preds = %if.then4.2, %if.then.2
  br i1 %tobool.not, label %for.inc.3, label %if.then.3

if.then.3:                                        ; preds = %for.inc.2
  %arrayidx.3 = getelementptr inbounds float, float* %a, i64 3
  %6 = load float, float* %arrayidx.3, align 4, !tbaa !3
  %arrayidx2.3 = getelementptr inbounds float, float* %b, i64 3
  %7 = load float, float* %arrayidx2.3, align 4, !tbaa !3
  %cmp3.3 = fcmp olt float %6, %7
  br i1 %cmp3.3, label %if.then4.3, label %for.inc.3

if.then4.3:                                       ; preds = %if.then.3
  %arrayidx8.3 = getelementptr inbounds float, float* %c, i64 3
  store float %6, float* %arrayidx8.3, align 4, !tbaa !3
  br label %for.inc.3

for.inc.3:                                        ; preds = %for.inc.1, %entry, %for.inc, %if.then4.3, %if.then.3, %for.inc.2
  ret void
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"float", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
