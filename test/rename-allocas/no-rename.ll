; RUN: %opt -rename-allocas %s -S | FileCheck %s

; Should fail to rename in this case because out-of-lifetime address computation

; CHECK: entry:
; CHECK-NEXT:   %t = alloca [100 x i32], align 16
; CHECK-NEXT:   %0 = bitcast [100 x i32]* %t to i8*
; CHECK-NEXT:   %arraydecay = getelementptr inbounds [100 x i32], [100 x i32]* %t, i64 0, i64 0
; CHECK-NEXT:   call void @llvm.lifetime.start.p0i8(i64 400, i8* nonnull %0) #3
; CHECK-NEXT:   call void @bar(i32* nonnull %arraydecay) #3
; CHECK-NEXT:   call void @llvm.lifetime.end.p0i8(i64 400, i8* nonnull %0) #3
; CHECK-NEXT:   call void @llvm.lifetime.start.p0i8(i64 400, i8* nonnull %0) #3
; CHECK-NEXT:   call void @bar(i32* nonnull %arraydecay) #3
; CHECK-NEXT:   call void @llvm.lifetime.end.p0i8(i64 400, i8* nonnull %0) #3
; CHECK-NEXT:   call void @llvm.lifetime.start.p0i8(i64 400, i8* nonnull %0) #3
; CHECK-NEXT:   call void @bar(i32* nonnull %arraydecay) #3
; CHECK-NEXT:   call void @llvm.lifetime.end.p0i8(i64 400, i8* nonnull %0) #3
; CHECK-NEXT:   call void @llvm.lifetime.start.p0i8(i64 400, i8* nonnull %0) #3
; CHECK-NEXT:   call void @bar(i32* nonnull %arraydecay) #3
; CHECK-NEXT:   call void @llvm.lifetime.end.p0i8(i64 400, i8* nonnull %0) #3
; CHECK-NEXT:   ret void

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nounwind ssp uwtable
define dso_local void @foo() local_unnamed_addr #0 {
entry:
  %t = alloca [100 x i32], align 16
  %0 = bitcast [100 x i32]* %t to i8*
  %arraydecay = getelementptr inbounds [100 x i32], [100 x i32]* %t, i64 0, i64 0
  call void @llvm.lifetime.start.p0i8(i64 400, i8* nonnull %0) #3
  call void @bar(i32* nonnull %arraydecay) #3
  call void @llvm.lifetime.end.p0i8(i64 400, i8* nonnull %0) #3
  call void @llvm.lifetime.start.p0i8(i64 400, i8* nonnull %0) #3
  call void @bar(i32* nonnull %arraydecay) #3
  call void @llvm.lifetime.end.p0i8(i64 400, i8* nonnull %0) #3
  call void @llvm.lifetime.start.p0i8(i64 400, i8* nonnull %0) #3
  call void @bar(i32* nonnull %arraydecay) #3
  call void @llvm.lifetime.end.p0i8(i64 400, i8* nonnull %0) #3
  call void @llvm.lifetime.start.p0i8(i64 400, i8* nonnull %0) #3
  call void @bar(i32* nonnull %arraydecay) #3
  call void @llvm.lifetime.end.p0i8(i64 400, i8* nonnull %0) #3
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

declare void @bar(i32*) local_unnamed_addr #2

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

attributes #0 = { nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nofree nosync nounwind willreturn }
attributes #2 = { "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
