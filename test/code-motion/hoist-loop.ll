; RUN: %opt -test-code-motion -inst-group=a,b %s -o - -S | FileCheck %s

; CHECK: if.end:
; CHECK-NEXT:  %x = phi i32 [ %x.lcssa, %exit ], [ undef, %entry ]
; CHECK-NEXT:  %y = phi i32 [ %y.lcssa, %exit ], [ undef, %entry ]
; CHECK-NEXT:  %a = add i32 %x, 1
; CHECK-NEXT:  %b = add i32 %y, 1

define dso_local void @foo() {
entry:
  %cond = icmp eq i32 0, 0
  br i1 %cond, label %preheader, label %if.end

preheader:
  br label %header

header:
  %x0 = load i32, i32* undef
  br i1 false, label %header, label %exit

exit:
  %x.lcssa = phi i32 [ %x0, %header ]
  br label %if.end

if.end:
  %x = phi i32 [ %x.lcssa, %exit ], [ undef, %entry ]
  %a = add i32 %x, 1
  br i1 %cond, label %preheader2, label %if.end2

preheader2:
  br label %header2

header2:
  %y0 = load i32, i32* undef
  br i1 false, label %header2, label %exit2

exit2:
  %y.lcssa = phi i32 [ %y0, %header2 ]
  br label %if.end2

if.end2:
  %y = phi i32 [ %y.lcssa, %exit2 ], [ undef, %if.end ]
  %b = add i32 %y, 1
  ret void
}
