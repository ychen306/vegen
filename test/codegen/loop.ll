; RUN: %opt -gslp -reschedule-scalar -no-unroll %s -S | FileCheck %s

; CHECK:   call void (...) @init()
; CHECK-NEXT:   %call3 = call i32 (...) @cont()
; CHECK-NEXT:   %tobool.not4 = icmp eq i32 %call3, 0
; CHECK-NEXT:   br i1 %tobool.not4, label %[[NO_LOOP:.*]], label %[[LOOP:.*]]

; CHECK: [[NO_LOOP]]:
; CHECK-NEXT:   br label %[[DONE:.*]]

; CHECK: [[LOOP]]:
; CHECK-NEXT:   br label %[[HEADER:.*]]

; CHECK: [[HEADER]]:
; CHECK-NEXT:   %call1 = call i32 (...) @cond()
; CHECK-NEXT:   %tobool2.not = icmp eq i32 %call1, 0
; CHECK-NEXT:   br i1 %tobool2.not, label %[[CALL_G:.*]], label %[[CALL_F:.*]]

; CHECK: [[LATCH:.*]]:
; CHECK-NEXT:   br i1 [[CONT:%.*]], label %[[HEADER]], label %[[EXIT:.*]]

; CHECK: [[EXIT]]:
; CHECK-NEXT:   br label %[[DONE]]

; CHECK: [[CALL_G]]:
; CHECK-NEXT:   call void (...) @g()
; CHECK-NEXT:   br label %[[JOIN:.*]]

; CHECK: [[CALL_F]]:
; CHECK-NEXT:   call void (...) @f()
; CHECK-NEXT:   br label %[[JOIN]]

; CHECK: [[JOIN]]:
; CHECK-NEXT:   call void (...) @h()
; CHECK-NEXT:   call void (...) @next()
; CHECK-NEXT:   %call = call i32 (...) @cont()
; CHECK-NEXT:   %tobool.not = icmp eq i32 %call, 0
; CHECK-NEXT:   br i1 %tobool.not, label %[[IF_TRUE:.*]], label %[[IF_FALSE:.*]]

; CHECK: [[IF_TRUE]]:
; CHECK-NEXT:   br label %[[MERGE:.*]]

; CHECK: [[IF_FALSE]]:
; CHECK-NEXT:   br label %[[MERGE]]

; CHECK: [[MERGE]]:
; CHECK-NEXT:   [[CONT]] = phi i1 [ false, %[[IF_TRUE]] ], [ true, %[[IF_FALSE]] ]
; CHECK-NEXT:   br label %[[LATCH]]

; CHECK: [[DONE]]:
; CHECK-NEXT:   ret void


target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nounwind ssp uwtable
define dso_local void @foo() local_unnamed_addr #0 {
entry:
  call void (...) @init() #2
  %call3 = call i32 (...) @cont() #2
  %tobool.not4 = icmp eq i32 %call3, 0
  br i1 %tobool.not4, label %for.end, label %for.body.preheader

for.body.preheader:                               ; preds = %entry
  br label %for.body

for.body:                                         ; preds = %for.body.preheader, %if.end
  %call1 = call i32 (...) @cond() #2
  %tobool2.not = icmp eq i32 %call1, 0
  br i1 %tobool2.not, label %if.else, label %if.then

if.then:                                          ; preds = %for.body
  call void (...) @f() #2
  br label %if.end

if.else:                                          ; preds = %for.body
  call void (...) @g() #2
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  call void (...) @h() #2
  call void (...) @next() #2
  %call = call i32 (...) @cont() #2
  %tobool.not = icmp eq i32 %call, 0
  br i1 %tobool.not, label %for.end.loopexit, label %for.body, !llvm.loop !3

for.end.loopexit:                                 ; preds = %if.end
  br label %for.end

for.end:                                          ; preds = %for.end.loopexit, %entry
  ret void
}

declare void @init(...) local_unnamed_addr #1

declare i32 @cont(...) local_unnamed_addr #1

declare i32 @cond(...) local_unnamed_addr #1

declare void @f(...) local_unnamed_addr #1

declare void @g(...) local_unnamed_addr #1

declare void @h(...) local_unnamed_addr #1

declare void @next(...) local_unnamed_addr #1

attributes #0 = { nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = distinct !{!3, !4, !5}
!4 = !{!"llvm.loop.mustprogress"}
!5 = !{!"llvm.loop.unroll.disable"}
