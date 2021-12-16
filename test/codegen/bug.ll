; RUN: %opt -gslp -test-codegen %s | lli | FileCheck %s

; CHECK: 5

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@h = external dso_local local_unnamed_addr global i32, align 4
@c = external dso_local local_unnamed_addr global i32, align 4
@.str.1 = private unnamed_addr constant [4 x i8] c"wtf\00", align 1
@.str.2 = private unnamed_addr constant [4 x i8] c"%X\0A\00", align 1
@b = dso_local local_unnamed_addr global i32 0, align 4
@a = dso_local local_unnamed_addr global [6 x i32] zeroinitializer, align 16
@d = dso_local local_unnamed_addr global i32 0, align 4

define dso_local i32 @main() local_unnamed_addr {
entry:
  br label %if.end

if.end:                                           ; preds = %entry
  br label %for.cond3.preheader

for.cond3.preheader:                              ; preds = %if.end
  %tobool.not.i = icmp eq i32 0, 0
  br i1 %tobool.not.i, label %for.body4.us.preheader, label %for.body4.preheader

for.body4.preheader:                              ; preds = %for.cond3.preheader
  br label %if.end8

for.body4.us.preheader:                           ; preds = %for.cond3.preheader
  %0 = load i32, i32* @b, align 4, !tbaa !0
  %idxprom.i.us = sext i32 %0 to i64
  %arrayidx.i.us = getelementptr inbounds [6 x i32], [6 x i32]* @a, i64 0, i64 %idxprom.i.us
  %1 = load i32, i32* %arrayidx.i.us, align 4, !tbaa !0
  %2 = load i32, i32* @d, align 4, !tbaa !0
  %xor.i.us = xor i32 %2, %0
  %idxprom1.i.us = sext i32 %xor.i.us to i64
  %arrayidx2.i.us = getelementptr inbounds [6 x i32], [6 x i32]* @a, i64 0, i64 %idxprom1.i.us
  %3 = load i32, i32* %arrayidx2.i.us, align 4, !tbaa !0
  %xor3.i.us = xor i32 %2, %1
  %xor4.i.us = xor i32 %xor3.i.us, %3
  %idxprom5.i.us = sext i32 %xor4.i.us to i64
  %arrayidx6.i.us = getelementptr inbounds [6 x i32], [6 x i32]* @a, i64 0, i64 %idxprom5.i.us
  %4 = load i32, i32* %arrayidx6.i.us, align 4, !tbaa !0
  %5 = xor i32 %2, %4
  %xor8.i.us = xor i32 %5, 5
  %idxprom9.i.us = sext i32 %xor8.i.us to i64
  %arrayidx10.i.us = getelementptr inbounds [6 x i32], [6 x i32]* @a, i64 0, i64 %idxprom9.i.us
  %6 = load i32, i32* %arrayidx10.i.us, align 4, !tbaa !0
  %xor11.i.us = xor i32 %6, 5
  br i1 true, label %if.end8.us, label %if.then6.us

if.then6.us:                                      ; preds = %for.body4.us.preheader
  %.pre = load i32, i32* @b, align 4, !tbaa !0
  br label %if.end8.us

if.end8.us:                                       ; preds = %if.then6.us, %for.body4.us.preheader
  %7 = phi i32 [ %.pre, %if.then6.us ], [ %xor11.i.us, %for.body4.us.preheader ]
  %8 = load i32, i32* @b, align 4, !tbaa !0
  %idxprom.i.us.1 = sext i32 %8 to i64
  %arrayidx.i.us.1 = getelementptr inbounds [6 x i32], [6 x i32]* @a, i64 0, i64 %idxprom.i.us.1
  %9 = load i32, i32* %arrayidx.i.us.1, align 4, !tbaa !0
  %10 = load i32, i32* @d, align 4, !tbaa !0
  %xor.i.us.1 = xor i32 %10, %8
  %idxprom1.i.us.1 = sext i32 %xor.i.us.1 to i64
  %arrayidx2.i.us.1 = getelementptr inbounds [6 x i32], [6 x i32]* @a, i64 0, i64 %idxprom1.i.us.1
  %11 = load i32, i32* %arrayidx2.i.us.1, align 4, !tbaa !0
  %xor3.i.us.1 = xor i32 %10, %9
  %xor4.i.us.1 = xor i32 %xor3.i.us.1, %11
  %idxprom5.i.us.1 = sext i32 %xor4.i.us.1 to i64
  %arrayidx6.i.us.1 = getelementptr inbounds [6 x i32], [6 x i32]* @a, i64 0, i64 %idxprom5.i.us.1
  %12 = load i32, i32* %arrayidx6.i.us.1, align 4, !tbaa !0
  %13 = xor i32 %10, %12
  %xor8.i.us.1 = xor i32 %13, 5
  %idxprom9.i.us.1 = sext i32 %xor8.i.us.1 to i64
  %arrayidx10.i.us.1 = getelementptr inbounds [6 x i32], [6 x i32]* @a, i64 0, i64 %idxprom9.i.us.1
  %14 = load i32, i32* %arrayidx10.i.us.1, align 4, !tbaa !0
  %xor11.i.us.1 = xor i32 %14, 5
  br i1 true, label %if.end8.us.1, label %if.then6.us.1

if.end8:                                          ; preds = %for.body4.preheader
  br label %if.end8.1

for.end12:                                        ; preds = %if.end8.3, %if.end8.us.3
  ret i32 0

if.then6.us.1:                                    ; preds = %if.end8.us
  %.pre21 = load i32, i32* @b, align 4, !tbaa !0
  br label %if.end8.us.1

if.end8.us.1:                                     ; preds = %if.then6.us.1, %if.end8.us
  %15 = phi i32 [ %.pre21, %if.then6.us.1 ], [ %xor11.i.us.1, %if.end8.us ]
  %call9.us.1 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.2, i64 0, i64 0), i32 %15)
  br label %if.end8.us.2

if.end8.us.2:                                     ; preds = %if.end8.us.1
  br label %if.end8.us.3

if.end8.us.3:                                     ; preds = %if.end8.us.2
  br label %for.end12

if.end8.1:                                        ; preds = %if.end8
  br label %if.end8.2

if.end8.2:                                        ; preds = %if.end8.1
  br label %if.end8.3

if.end8.3:                                        ; preds = %if.end8.2
  br label %for.end12
}

declare i32 @printf(i8*, ...) local_unnamed_addr

!0 = !{!1, !1, i64 0}
!1 = !{!"int", !2, i64 0}
!2 = !{!"omnipotent char", !3, i64 0}
!3 = !{!"Simple C/C++ TBAA"}
