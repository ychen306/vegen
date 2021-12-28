; RUN: %opt -gslp -test-codegen %s | lli

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@c = dso_local global i32 7, align 4
@b = dso_local local_unnamed_addr global i32 2080555006, align 4

define dso_local i32 @main() local_unnamed_addr #0 {
entry:
  %0 = load i32, i32* @b, align 4, !tbaa !0
  br i1 zeroinitializer, label %for.body.us.preheader.i, label %l.exit

for.body.us.preheader.i:                          ; preds = %entry
  br i1 zeroinitializer, label %for.inc10.loopexit.us.2.i, label %for.body3.lr.ph.us.i

for.body3.us.i:                                   ; preds = %for.body3.lr.ph.us.i, %for.inc.us.i
  %tobool4.not.us.i = icmp eq i32 zeroinitializer, 0
  br i1 %tobool4.not.us.i, label %for.inc.us.i, label %cleanup.loopexit.i

for.inc.us.i:                                     ; preds = %for.body3.us.i
  br i1 zeroinitializer, label %for.body3.us.i, label %for.cond1.for.inc10.loopexit_crit_edge.us.i, !llvm.loop !4

for.body3.lr.ph.us.i:                             ; preds = %for.body.us.preheader.i
  br label %for.body3.us.i

for.cond1.for.inc10.loopexit_crit_edge.us.i:      ; preds = %for.inc.us.i
  br label %for.inc10.loopexit.us.2.i

cleanup.loopexit.i:                               ; preds = %for.body3.us.i
  br label %l.exit

for.inc10.loopexit.us.2.i:                        ; preds = %for.cond1.for.inc10.loopexit_crit_edge.us.i, %for.body.us.preheader.i
  store i32 0, i32* @c, align 4, !tbaa !0
  br label %l.exit

l.exit:                                           ; preds = %for.inc10.loopexit.us.2.i, %cleanup.loopexit.i, %entry
  br label %if.end

if.end:                                           ; preds = %l.exit
  ret i32 0
}

attributes #0 = { "frame-pointer"="all" }

!0 = !{!1, !1, i64 0}
!1 = !{!"int", !2, i64 0}
!2 = !{!"omnipotent char", !3, i64 0}
!3 = !{!"Simple C/C++ TBAA"}
!4 = distinct !{!4, !5}
!5 = !{!"llvm.loop.mustprogress"}
