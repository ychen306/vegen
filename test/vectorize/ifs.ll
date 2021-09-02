; RUN: %opt -gslp %s -o - -S | FileCheck %s

; CHECK: if.then:
; CHECK-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %a, i64 0
; CHECK-NEXT:   [[A:%.*]] = bitcast i32* %arrayidx to <2 x i32>*
; CHECK-NEXT:   store <2 x i32> <i32 0, i32 1>, <2 x i32>* [[A]], align 4, !tbaa !3

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define dso_local void @foo(i32 %x, i32 %y, i32* %a) #0 {
entry:
  %cmp = icmp slt i32 %x, %y
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %arrayidx = getelementptr inbounds i32, i32* %a, i64 0
  store i32 0, i32* %arrayidx, align 4, !tbaa !3
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %cmp1 = icmp slt i32 %x, %y
  br i1 %cmp, label %if.then2, label %if.end4

if.then2:                                         ; preds = %if.end
  %arrayidx3 = getelementptr inbounds i32, i32* %a, i64 1
  store i32 1, i32* %arrayidx3, align 4, !tbaa !3
  br label %if.end4

if.end4:                                          ; preds = %if.then2, %if.end
  ret void
}

attributes #0 = { nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
