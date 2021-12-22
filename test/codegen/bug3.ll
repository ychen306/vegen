; RUN: %opt -gslp -test-codegen %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define dso_local void @e() local_unnamed_addr {
entry:
  br i1 undef, label %for.end5, label %for.body.lr.ph

for.body.lr.ph:                                   ; preds = %entry
  br label %for.body.lr.ph.split

for.body.lr.ph.split:                             ; preds = %for.body.lr.ph
  br i1 undef, label %for.end5, label %for.body

for.body:                                         ; preds = %for.body.lr.ph.split
  br label %for.body4

for.body4:                                        ; preds = %for.body4, %for.body
  br label %for.body4

for.end5:                                         ; preds = %for.body.lr.ph.split, %entry
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #0

attributes #0 = { argmemonly nofree nosync nounwind willreturn }
