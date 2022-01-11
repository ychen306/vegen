; RUN: %opt -gslp -no-unroll %s -o /dev/null

source_filename = "small.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @kake2hiku() local_unnamed_addr #0 {
entry:
  br label %do.body

do.body:                                          ; preds = %do.cond.3, %entry
  %a.0 = phi i8* [ undef, %entry ], [ %incdec.ptr.3, %do.cond.3 ]
  %0 = load i8, i8* %a.0, align 1, !tbaa !3
  %cmp = icmp eq i8 %0, 42
  br i1 %cmp, label %if.then, label %do.cond

if.then:                                          ; preds = %do.body
  store i8 45, i8* %a.0, align 1, !tbaa !3
  br label %do.cond

do.cond:                                          ; preds = %if.then, %do.body
  %1 = phi i8 [ %0, %do.body ], [ 45, %if.then ]
  %incdec.ptr = getelementptr inbounds i8, i8* %a.0, i64 1
  %tobool.not = icmp eq i8 %1, 0
  br i1 %tobool.not, label %do.end, label %do.body.1, !llvm.loop !6

do.end:                                           ; preds = %do.cond.3, %do.cond.2, %do.cond.1, %do.cond
  ret void

do.body.1:                                        ; preds = %do.cond
  %2 = load i8, i8* %incdec.ptr, align 1, !tbaa !3
  %cmp.1 = icmp eq i8 %2, 42
  br i1 %cmp.1, label %if.then.1, label %do.cond.1

if.then.1:                                        ; preds = %do.body.1
  store i8 45, i8* %incdec.ptr, align 1, !tbaa !3
  br label %do.cond.1

do.cond.1:                                        ; preds = %if.then.1, %do.body.1
  %3 = phi i8 [ %2, %do.body.1 ], [ 45, %if.then.1 ]
  %incdec.ptr.1 = getelementptr inbounds i8, i8* %incdec.ptr, i64 1
  %tobool.not.1 = icmp eq i8 %3, 0
  br i1 %tobool.not.1, label %do.end, label %do.body.2, !llvm.loop !6

do.body.2:                                        ; preds = %do.cond.1
  %4 = load i8, i8* %incdec.ptr.1, align 1, !tbaa !3
  %cmp.2 = icmp eq i8 %4, 42
  br i1 %cmp.2, label %if.then.2, label %do.cond.2

if.then.2:                                        ; preds = %do.body.2
  store i8 45, i8* %incdec.ptr.1, align 1, !tbaa !3
  br label %do.cond.2

do.cond.2:                                        ; preds = %if.then.2, %do.body.2
  %5 = phi i8 [ %4, %do.body.2 ], [ 45, %if.then.2 ]
  %incdec.ptr.2 = getelementptr inbounds i8, i8* %incdec.ptr.1, i64 1
  %tobool.not.2 = icmp eq i8 %5, 0
  br i1 %tobool.not.2, label %do.end, label %do.body.3, !llvm.loop !6

do.body.3:                                        ; preds = %do.cond.2
  %6 = load i8, i8* %incdec.ptr.2, align 1, !tbaa !3
  %cmp.3 = icmp eq i8 %6, 42
  br i1 %cmp.3, label %if.then.3, label %do.cond.3

if.then.3:                                        ; preds = %do.body.3
  store i8 45, i8* %incdec.ptr.2, align 1, !tbaa !3
  br label %do.cond.3

do.cond.3:                                        ; preds = %if.then.3, %do.body.3
  %7 = phi i8 [ %6, %do.body.3 ], [ 45, %if.then.3 ]
  %incdec.ptr.3 = getelementptr inbounds i8, i8* %incdec.ptr.2, i64 1
  %tobool.not.3 = icmp eq i8 %7, 0
  br i1 %tobool.not.3, label %do.end, label %do.body, !llvm.loop !6
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"omnipotent char", !5, i64 0}
!5 = !{!"Simple C/C++ TBAA"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
