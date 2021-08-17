; RUN: %opt -test-code-motion -inst-group=x,y -inst-group=a,b %s -o - -S | FileCheck %s

; CHECK: entry:
; CHECK-NEXT: {{.*}} = load i32, i32* undef
; CHECK-NEXT: {{.*}} = load i32, i32* undef

; CHECK: if.then:
; CHECK-NEXT: %a = add i32 1, 2
; CHECK-NEXT: %b = add i32 %x, 3
; CHECK-NEXT: br label %if.end

define dso_local void @foo() {
entry:
  br i1 undef, label %if.then, label %if.end

if.then:
  %a = add i32 1, 2
  br label %if.end

if.end:
  %x = load i32, i32* undef
  br i1 undef, label %if.then2, label %if.end2

if.then2:
  %b = add i32 %x, 3
  br label %if.end2

if.end2:
  %y = load i32, i32* undef
  ret void
}
