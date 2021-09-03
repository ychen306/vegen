; RUN: %opt -gslp %s -o - -S | FileCheck %s

; CHECK: entry:
; CHECK-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %b, i64 0
; CHECK-NEXT:   [[B0_ADDR:%.*]] = bitcast i32* %arrayidx to <2 x i32>*
; CHECK-NEXT:   [[B0:%.*]] = load <2 x i32>, <2 x i32>* [[B0_ADDR]]
; CHECK-NEXT:   %tobool = icmp ne i32 %x, 0
; CHECK-NEXT:   br i1 %tobool, label %if.then, label %if.else

; CHECK: if.then:
; CHECK-NEXT:   %arrayidx1 = getelementptr inbounds i32, i32* %b, i64 100
; CHECK-NEXT:   [[B100_ADDR:%.*]] = bitcast i32* %arrayidx1 to <2 x i32>*
; CHECK-NEXT:   [[B100:%.*]] = load <2 x i32>, <2 x i32>* [[B100_ADDR]]
; CHECK-NEXT:   [[ADD1:%.*]] = add <2 x i32> [[B100]], [[B0]]
; CHECK-NEXT:   br label %if.end

; CHECK: if.else:
; CHECK-NEXT:   %arrayidx2 = getelementptr inbounds i32, i32* %b, i64 200
; CHECK-NEXT:   [[B200_ADDR:%.*]] = bitcast i32* %arrayidx2 to <2 x i32>*
; CHECK-NEXT:   [[B200:%.*]] = load <2 x i32>, <2 x i32>* [[B200_ADDR]]
; CHECK-NEXT:   [[ADD2:%.*]] = add <2 x i32> [[B200]], [[B0]]
; CHECK-NEXT:   br label %if.end

; CHECK: if.end:
; CHECK-NEXT:   [[PHI:%.*]] = phi <2 x i32> [ [[ADD1]], %if.then ], [ [[ADD2]], %if.else ]
; CHECK-NEXT:   %tobool5 = icmp ne i32 %x, 0
; CHECK-NEXT:   br i1 %tobool5, label %if.then6, label %if.else9

; CHECK: if.end12:
; CHECK-NEXT:   %arrayidx13 = getelementptr inbounds i32, i32* %a, i64 0
; CHECK-NEXT:   [[A:%.*]] = bitcast i32* %arrayidx13 to <2 x i32>*
; CHECK-NEXT:   store <2 x i32> [[PHI]], <2 x i32>* [[A]]

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nounwind ssp uwtable
define dso_local void @foo(i32 %x, i32* noalias %a, i32* noalias %b) #0 {
entry:
  %arrayidx = getelementptr inbounds i32, i32* %b, i64 0
  %0 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %tobool = icmp ne i32 %x, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %arrayidx1 = getelementptr inbounds i32, i32* %b, i64 100
  %1 = load i32, i32* %arrayidx1, align 4, !tbaa !3
  %add = add nsw i32 %1, %0
  br label %if.end

if.else:                                          ; preds = %entry
  %arrayidx2 = getelementptr inbounds i32, i32* %b, i64 200
  %2 = load i32, i32* %arrayidx2, align 4, !tbaa !3
  %add3 = add nsw i32 %2, %0
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %v1.0 = phi i32 [ %add, %if.then ], [ %add3, %if.else ]
  %arrayidx4 = getelementptr inbounds i32, i32* %b, i64 1
  %3 = load i32, i32* %arrayidx4, align 4, !tbaa !3
  %tobool5 = icmp ne i32 %x, 0
  br i1 %tobool5, label %if.then6, label %if.else9

if.then6:                                         ; preds = %if.end
  %arrayidx7 = getelementptr inbounds i32, i32* %b, i64 101
  %4 = load i32, i32* %arrayidx7, align 4, !tbaa !3
  %add8 = add nsw i32 %4, %3
  br label %if.end12

if.else9:                                         ; preds = %if.end
  %arrayidx10 = getelementptr inbounds i32, i32* %b, i64 201
  %5 = load i32, i32* %arrayidx10, align 4, !tbaa !3
  %add11 = add nsw i32 %5, %3
  br label %if.end12

if.end12:                                         ; preds = %if.else9, %if.then6
  %v2.0 = phi i32 [ %add8, %if.then6 ], [ %add11, %if.else9 ]
  %arrayidx13 = getelementptr inbounds i32, i32* %a, i64 0
  store i32 %v1.0, i32* %arrayidx13, align 4, !tbaa !3
  %arrayidx14 = getelementptr inbounds i32, i32* %a, i64 1
  store i32 %v2.0, i32* %arrayidx14, align 4, !tbaa !3
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
