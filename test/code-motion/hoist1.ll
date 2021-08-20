; RUN: %opt -test-code-motion -inst-group=a,b %s -o - -S | FileCheck %s
; RUN: %opt -test-code-motion -gather -inst-group=a,b %s -o - -S | FileCheck %s

; CHECK: if.then:
; CHECK-NEXT: %a = add i32 1, 2
; CHECK-NEXT: %b = add i32 3, 4
; CHECK-NEXT: br label %if.end

define dso_local void @foo() {
entry:
  br i1 undef, label %if.then, label %if.end

if.then:
  %a = add i32 1, 2
  br label %if.end

if.end:
  br i1 undef, label %if.then2, label %if.end2

if.then2:
  %b = add i32 3, 4
  br label %if.end2

if.end2:
  ret void
}
