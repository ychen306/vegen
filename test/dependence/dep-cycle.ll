; RUN: %opt -gslp -test-codegen %s -o /dev/null

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define dso_local i32 @c() local_unnamed_addr {
if.end.preheader:
  br label %if.end

if.end:                                           ; preds = %if.end, %if.end.preheader
  %f.05 = phi i8 [ %e.04, %if.end ], [ zeroinitializer, %if.end.preheader ]
  %e.04 = phi i8 [ %f.05, %if.end ], [ zeroinitializer, %if.end.preheader ]
  br i1 zeroinitializer, label %if.end, label %while.end

while.end:                                        ; preds = %if.end
  ret i32 zeroinitializer
}
