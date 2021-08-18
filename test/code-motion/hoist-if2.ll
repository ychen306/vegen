; RUN: %opt -test-code-motion -inst-group=a,b %s -o - -S | FileCheck %s

; CHECK: if.end:
; CHECK-NEXT:  %x = phi i32 [ 0, %if.then ], [ 1, %entry ]
; CHECK-NEXT:  %y = phi i32 [ %dep, %if.then ], [ 3, %entry ]
; CHECK-NEXT:  %a = add i32 %x, 1
; CHECK-NEXT:  %b = add i32 %y, 2

define dso_local void @foo() {
entry:
  br i1 undef, label %if.then, label %if.end

if.then:
  br label %if.end

if.end:
  %x = phi i32 [ 0, %if.then ], [ 1, %entry ]
  %a = add i32 %x, 1
  %dep = load i32, i32* undef
  br i1 undef, label %if.then2, label %if.end2

if.then2:
  br label %if.end2

if.end2:
  %y = phi i32 [ %dep, %if.then2 ], [ 3, %if.end ]
  %b = add i32 %y, 2
  ret void
}
