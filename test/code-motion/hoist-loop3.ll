; RUN: %opt -test-code-motion -inst-group=a,b %s -o - -S | FileCheck %s

; CHECK: {{^}}header:
; CHECK-NEXT:   %x0 = phi i32 [ 0, %preheader2 ], [ %x0.next, %header2 ]
; CHECK-NEXT:   %y0 = phi i32 [ 0, %preheader2 ], [ %y0.next, %header2 ]
; CHECK-NEXT:   %t0 = load i32, i32* undef
; CHECK-NEXT:   %t1 = add i32 %t0, 1
; CHECK-NEXT:   %x0.next = add i32 %x0, %t1
; CHECK-NEXT:   %t2 = load i32, i32* undef
; CHECK-NEXT:   %t3 = add i32 %t2, 2
; CHECK-NEXT:   %y0.next = add i32 %y0, %t3

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
  %x0 = phi i32 [ 0, %preheader ], [ %x0.next, %header ]
  %t0 = load i32, i32* undef
  %t1 = add i32 %t0, 1
  %x0.next = add i32 %x0, %t1
  br i1 false, label %header, label %exit

exit:
  %x.lcssa = phi i32 [ %x0.next, %header ]
  br label %if.end

if.end:
  %x = phi i32 [ %x.lcssa, %exit ], [ undef, %entry ]
  %a = add i32 %x, 1
  br i1 %cond, label %preheader2, label %if.end2

preheader2:
  br label %header2

header2:
  %y0 = phi i32 [ 0, %preheader2 ], [ %y0.next, %header2 ]
  %t2 = load i32, i32* undef
  %t3 = add i32 %t2, 2
  %y0.next = add i32 %y0, %t3
  br i1 false, label %header2, label %exit2

exit2:
  %y.lcssa = phi i32 [ %y0.next, %header2 ]
  br label %if.end2

if.end2:
  %y = phi i32 [ %y.lcssa, %exit2 ], [ undef, %if.end ]
  %b = add i32 %y, 1
  ret void
}
