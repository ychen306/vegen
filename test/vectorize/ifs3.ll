; RUN: %opt -gslp %s -o - -S | FileCheck %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; CHECK: if.then:
; CHECK-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %b, i64 0
; CHECK-NEXT:   [[B_ADDR:%.*]] = bitcast i32* %arrayidx to <2 x i32>*
; CHECK-NEXT:   [[B:%.*]] = load <2 x i32>, <2 x i32>* [[B_ADDR]]
; CHECK-NEXT:   br label %if.end

; CHECK: if.else:
; CHECK-NEXT:   %arrayidx1 = getelementptr inbounds i32, i32* %c, i64 0
; CHECK-NEXT:   [[C_ADDR:%.*]] = bitcast i32* %arrayidx1 to <2 x i32>*
; CHECK-NEXT:   [[C:%.*]] = load <2 x i32>, <2 x i32>* [[C_ADDR]]
; CHECK-NEXT:   br label %if.end

; CHECK: if.end:
; CHECK-NEXT:   [[PHI:%.*]] = phi <2 x i32> [ [[B]], %if.then ], [ [[C]], %if.else ]
; CHECK-NEXT:   %tobool2 = icmp ne i32 %x, 0
; CHECK-NEXT:   br i1 %tobool2, label %if.then3, label %if.else5

; CHECK: if.end7:
; CHECK-NEXT:   %arrayidx8 = getelementptr inbounds i32, i32* %a, i64 0
; CHECK-NEXT:   [[A:%.*]] = bitcast i32* %arrayidx8 to <2 x i32>*
; CHECK-NEXT:   store <2 x i32> [[PHI]], <2 x i32>* [[A]]

; Function Attrs: nounwind ssp uwtable
define dso_local void @foo(i32 %x, i32* noalias %a, i32* noalias %b, i32* noalias %c) #0 {
entry:
  %tobool = icmp ne i32 %x, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %arrayidx = getelementptr inbounds i32, i32* %b, i64 0
  %0 = load i32, i32* %arrayidx, align 4, !tbaa !3
  br label %if.end

if.else:                                          ; preds = %entry
  %arrayidx1 = getelementptr inbounds i32, i32* %c, i64 0
  %1 = load i32, i32* %arrayidx1, align 4, !tbaa !3
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %v1.0 = phi i32 [ %0, %if.then ], [ %1, %if.else ]
  %tobool2 = icmp ne i32 %x, 0
  br i1 %tobool2, label %if.then3, label %if.else5

if.then3:                                         ; preds = %if.end
  %arrayidx4 = getelementptr inbounds i32, i32* %b, i64 1
  %2 = load i32, i32* %arrayidx4, align 4, !tbaa !3
  br label %if.end7

if.else5:                                         ; preds = %if.end
  %arrayidx6 = getelementptr inbounds i32, i32* %c, i64 1
  %3 = load i32, i32* %arrayidx6, align 4, !tbaa !3
  br label %if.end7

if.end7:                                          ; preds = %if.else5, %if.then3
  %v2.0 = phi i32 [ %2, %if.then3 ], [ %3, %if.else5 ]
  %arrayidx8 = getelementptr inbounds i32, i32* %a, i64 0
  store i32 %v1.0, i32* %arrayidx8, align 4, !tbaa !3
  %arrayidx9 = getelementptr inbounds i32, i32* %a, i64 1
  store i32 %v2.0, i32* %arrayidx9, align 4, !tbaa !3
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
