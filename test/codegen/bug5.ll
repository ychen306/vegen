; RUN: %opt -gslp -test-codegen %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define dso_local i16 @f() local_unnamed_addr {
for.cond1thread-pre-split.lr.ph:
  %tobool4.not = icmp eq i32 undef, 0
  br i1 undef, label %for.cond1thread-pre-split.lr.ph.split, label %Flow37

Flow37:                                           ; preds = %for.end6.loopexit, %Flow, %for.cond1thread-pre-split.lr.ph
  %0 = phi i16 [ undef, %for.cond1thread-pre-split.lr.ph ], [ undef, %for.end6.loopexit ], [ undef, %Flow ]
  ret i16 undef

for.cond1thread-pre-split.lr.ph.split:            ; preds = %for.cond1thread-pre-split.lr.ph
  br i1 undef, label %if.then.split, label %Flow

Flow:                                             ; preds = %if.then.split, %for.cond1thread-pre-split.lr.ph.split
  %1 = phi i1 [ false, %if.then.split ], [ true, %for.cond1thread-pre-split.lr.ph.split ]
  br i1 %1, label %for.cond1thread-pre-split.us10.preheader, label %Flow37

for.cond1thread-pre-split.us10.preheader:         ; preds = %Flow
  br label %for.cond1thread-pre-split.us10

for.cond1thread-pre-split.us10:                   ; preds = %for.cond1thread-pre-split.us10, %for.cond1thread-pre-split.us10.preheader
  br i1 undef, label %for.end6.loopexit, label %for.cond1thread-pre-split.us10

if.then.split:                                    ; preds = %for.cond1thread-pre-split.lr.ph.split
  br label %Flow

for.end6.loopexit:                                ; preds = %for.cond1thread-pre-split.us10
  br label %Flow37
}
