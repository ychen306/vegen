; RUN: %opt -gslp -test-codegen %s | lli | FileCheck %s

; CHECK: 0

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@a = dso_local global i8 0, align 1
@d = dso_local global [3 x [1 x i8*]] [[1 x i8*] zeroinitializer, [1 x i8*] zeroinitializer, [1 x i8*] [i8* @a]], align 16
@e = dso_local local_unnamed_addr global i8** getelementptr inbounds ([3 x [1 x i8*]], [3 x [1 x i8*]]* @d, i64 0, i64 2, i64 0), align 8
@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1
@c = dso_local local_unnamed_addr global i8 0, align 1

define dso_local i32 @main() local_unnamed_addr {
entry:
  %0 = load i8**, i8*** @e, align 8, !tbaa !0
  %1 = load i8*, i8** %0, align 8, !tbaa !0
  %2 = load i8, i8* %1, align 1, !tbaa !4
  %tobool.not7.i = icmp eq i8 %2, 0
  br i1 %tobool.not7.i, label %entry.g.exit_crit_edge, label %for.cond.preheader.preheader.i

entry.g.exit_crit_edge:                           ; preds = %entry
  br label %g.exit

for.cond.preheader.preheader.i:                   ; preds = %entry
  br label %for.cond.preheader.i

h.loopexit.i.loopexit:                            ; preds = %for.body.i
  br label %h.loopexit.i

h.loopexit.i:                                     ; preds = %for.body.i.preheader, %h.loopexit.i.loopexit
  br i1 zeroinitializer, label %g.exit.loopexit15, label %for.cond.preheader.i

for.cond.preheader.i:                             ; preds = %h.loopexit.i, %for.cond.preheader.preheader.i
  br i1 zeroinitializer, label %g.exit.loopexit15, label %for.body.i.preheader

for.body.i.preheader:                             ; preds = %for.cond.preheader.i
  br i1 zeroinitializer, label %h.loopexit.i, label %if.then3.i.preheader

if.then3.i.preheader:                             ; preds = %for.body.i.preheader
  br label %for.body.i.lr.ph

for.body.i.lr.ph:                                 ; preds = %if.then3.i.preheader
  br label %for.body.i

for.body.i:                                       ; preds = %for.body.i.if.then3.i_crit_edge, %for.body.i.lr.ph
  br i1 zeroinitializer, label %h.loopexit.i.loopexit, label %for.body.i.if.then3.i_crit_edge, !llvm.loop !5

for.body.i.if.then3.i_crit_edge:                  ; preds = %for.body.i
  br i1 zeroinitializer, label %if.then3.i.g.exit.loopexit_crit_edge, label %for.body.i, !llvm.loop !5

if.then3.i.g.exit.loopexit_crit_edge:             ; preds = %for.body.i.if.then3.i_crit_edge
  br label %g.exit.loopexit

g.exit.loopexit:                                  ; preds = %if.then3.i.g.exit.loopexit_crit_edge
  br label %g.exit

g.exit.loopexit15:                                ; preds = %for.cond.preheader.i, %h.loopexit.i
  br label %g.exit

g.exit:                                           ; preds = %g.exit.loopexit15, %g.exit.loopexit, %entry.g.exit_crit_edge
  %3 = phi i8 [ zeroinitializer, %entry.g.exit_crit_edge ], [ 8, %g.exit.loopexit ], [ zeroinitializer, %g.exit.loopexit15 ]
  %conv = sext i8 %3 to i32
  %call = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i64 0, i64 0), i32 %conv)
  ret i32 0
}

declare i32 @printf(i8*, ...) local_unnamed_addr

!0 = !{!1, !1, i64 0}
!1 = !{!"any pointer", !2, i64 0}
!2 = !{!"omnipotent char", !3, i64 0}
!3 = !{!"Simple C/C++ TBAA"}
!4 = !{!2, !2, i64 0}
!5 = distinct !{!5, !6}
!6 = !{!"llvm.loop.mustprogress"}
