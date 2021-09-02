; RUN: %opt -gslp %s -o - -S | FileCheck %s

; CHECK: if.end:
; CHECK-NEXT:   [[PHI:%.*]] = phi <2 x i32> [ <i32 0, i32 2>, %if.then ], [ <i32 1, i32 3>, %if.else ]
; CHECK-NEXT:   %cmp1 = icmp slt i32 %x, %y
; CHECK-NEXT:   br i1 %cmp1, label %if.then2, label %if.else3

; CHECK:   [[A:%.*]] = bitcast i32* %arrayidx to <2 x i32>*
; CHECK-NEXT:   store <2 x i32> [[PHI]], <2 x i32>* [[A]]
; CHECK-NEXT:   ret void


target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nounwind ssp uwtable
define dso_local void @foo(i32 %x, i32 %y, i32* %a) #0 {
entry:
  %cmp = icmp slt i32 %x, %y
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %v1.0 = phi i32 [ 0, %if.then ], [ 1, %if.else ]
  %cmp1 = icmp slt i32 %x, %y
  br i1 %cmp1, label %if.then2, label %if.else3

if.then2:                                         ; preds = %if.end
  br label %if.end4

if.else3:                                         ; preds = %if.end
  br label %if.end4

if.end4:                                          ; preds = %if.else3, %if.then2
  %v2.0 = phi i32 [ 2, %if.then2 ], [ 3, %if.else3 ]
  %arrayidx = getelementptr inbounds i32, i32* %a, i64 0
  store i32 %v1.0, i32* %arrayidx, align 4, !tbaa !3
  %arrayidx5 = getelementptr inbounds i32, i32* %a, i64 1
  store i32 %v2.0, i32* %arrayidx5, align 4, !tbaa !3
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

attributes #0 = { nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nofree nosync nounwind willreturn }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
