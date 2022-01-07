; RUN: %opt -gslp -test-codegen %s -o /dev/null

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define dso_local i32 @d() local_unnamed_addr {
entry:
  br i1 false, label %cleanup8, label %if.then

if.then:                                          ; preds = %entry
  br i1 false, label %if.end, label %cleanup8.critedge

if.end:                                           ; preds = %if.then
  br label %UnifiedReturnBlock

cleanup8.critedge:                                ; preds = %if.then
  br label %cleanup8

cleanup8:                                         ; preds = %cleanup8.critedge, %entry
  br label %UnifiedReturnBlock

UnifiedReturnBlock:                               ; preds = %cleanup8, %if.end
  %UnifiedRetVal = phi i32 [ 0, %if.end ], [ 0, %cleanup8 ]
  ret i32 %UnifiedRetVal
}
