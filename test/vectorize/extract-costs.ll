; RUN: %opt -gslp -no-unroll %s -o /dev/null

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define dso_local void @c(i32* %mem) local_unnamed_addr {
entry:
  %arrayidx = getelementptr inbounds i32, i32* %mem, i64 1
  %arrayidx2 = getelementptr inbounds i32, i32* %mem, i64 2
  br label %do.body

do.body:                                          ; preds = %do.body, %entry
  %0 = phi i32 [ %1, %do.body ], [ 0, %entry ]
  %1 = phi i32 [ %0, %do.body ], [ 0, %entry ]
  br i1 true, label %do.end, label %do.body, !llvm.loop !0

do.end:                                           ; preds = %do.body
  %.lcssa9 = phi i32 [ %0, %do.body ]
  %.lcssa = phi i32 [ %1, %do.body ]
  store i32 %.lcssa9, i32* %arrayidx, align 4, !tbaa !2
  store i32 %.lcssa, i32* %arrayidx2, align 4, !tbaa !2
  ret void 
}

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}
!2 = !{!3, !3, i64 0}
!3 = !{!"int", !4, i64 0}
!4 = !{!"omnipotent char", !5, i64 0}
!5 = !{!"Simple C/C++ TBAA"}
