; RUN: %opt -gslp %s -o /dev/null

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

%struct.a = type { %struct.a*, %struct.a* }

@e = external dso_local local_unnamed_addr global %struct.a*, align 8

define dso_local i32 @h() local_unnamed_addr {
for.body.lr.ph:
  %conv = sitofp i32 zeroinitializer to double
  br i1 zeroinitializer, label %for.body.us.preheader, label %for.body.preheader

for.body.preheader:                               ; preds = %for.body.lr.ph
  br label %for.body

for.body.us.preheader:                            ; preds = %for.body.lr.ph
  br label %for.body.us

for.body.us:                                      ; preds = %for.body.us, %for.body.us.preheader
  br i1 zeroinitializer, label %for.cond.for.end7_crit_edge.loopexit, label %for.body.us, !llvm.loop !0

for.body:                                         ; preds = %for.end, %for.body.preheader
  %i.014 = phi i32 [ %i.1, %for.end ], [ zeroinitializer, %for.body.preheader ]
  %a.013 = phi double [ %a.1, %for.end ], [ zeroinitializer, %for.body.preheader ]
  br label %for.end

for.end:                                          ; preds = %for.body
  %div = fdiv double 0.000000e+00, %conv
  %cmp = fcmp ogt double %div, %a.013
  %a.1 = select i1 %cmp, double %div, double %a.013
  %i.1 = select i1 %cmp, i32 zeroinitializer, i32 %i.014
  br i1 zeroinitializer, label %for.cond.for.end7_crit_edge.loopexit1, label %for.body, !llvm.loop !3

for.cond.for.end7_crit_edge.loopexit:             ; preds = %for.body.us
  ret i32 zeroinitializer

for.cond.for.end7_crit_edge.loopexit1:            ; preds = %for.end
  ret i32 zeroinitializer
}

!0 = distinct !{!0, !1, !2}
!1 = !{!"llvm.loop.mustprogress"}
!2 = !{!"llvm.loop.unswitch.partial.disable"}
!3 = distinct !{!3, !1}
