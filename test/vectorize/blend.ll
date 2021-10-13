; RUN: %opt -gslp %s -S | FileCheck %s

; CHECK:  %0 = load <4 x float>, <4 x float>* bitcast ([4 x float]* @a to <4 x float>*)
; CHECK-NEXT:  %1 = load <4 x float>, <4 x float>* bitcast ([4 x float]* @b to <4 x float>*)
; CHECK-NEXT:  %2 = fcmp olt <4 x float> %0, %1
; CHECK-NEXT:  %3 = fsub <4 x float> %0, %1
; CHECK-NEXT:  %4 = fadd <4 x float> %0, %1
; CHECK-NEXT:  %5 = select <4 x i1> %2, <4 x float> %4, <4 x float> %3
; CHECK-NEXT:  store <4 x float> %5, <4 x float>* bitcast ([4 x float]* @c to <4 x float>*)
; CHECK-NEXT:  ret void

source_filename = "t.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@a = dso_local global [4 x float] zeroinitializer, align 16
@b = dso_local global [4 x float] zeroinitializer, align 16
@c = dso_local global [4 x float] zeroinitializer, align 16

; Function Attrs: nounwind ssp uwtable
define dso_local void @foo() #0 {
entry:
  %0 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 0), align 4, !tbaa !3
  %1 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @b, i64 0, i64 0), align 4, !tbaa !3
  %cmp3 = fcmp olt float %0, %1
  br i1 %cmp3, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %add = fadd float %0, %1
  br label %if.end

if.else:                                          ; preds = %entry
  %sub = fsub float %0, %1
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %x.0 = phi float [ %add, %if.then ], [ %sub, %if.else ]
  store float %x.0, float* getelementptr inbounds ([4 x float], [4 x float]* @c, i64 0, i64 0), align 4, !tbaa !3
  %2 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 1), align 4, !tbaa !3
  %3 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @b, i64 0, i64 1), align 4, !tbaa !3
  %cmp3.1 = fcmp olt float %2, %3
  br i1 %cmp3.1, label %if.then.1, label %if.else.1

if.else.1:                                        ; preds = %if.end
  %sub.1 = fsub float %2, %3
  br label %if.end.1

if.then.1:                                        ; preds = %if.end
  %add.1 = fadd float %2, %3
  br label %if.end.1

if.end.1:                                         ; preds = %if.then.1, %if.else.1
  %x.0.1 = phi float [ %add.1, %if.then.1 ], [ %sub.1, %if.else.1 ]
  store float %x.0.1, float* getelementptr inbounds ([4 x float], [4 x float]* @c, i64 0, i64 1), align 4, !tbaa !3
  %4 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 2), align 4, !tbaa !3
  %5 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @b, i64 0, i64 2), align 4, !tbaa !3
  %cmp3.2 = fcmp olt float %4, %5
  br i1 %cmp3.2, label %if.then.2, label %if.else.2

if.else.2:                                        ; preds = %if.end.1
  %sub.2 = fsub float %4, %5
  br label %if.end.2

if.then.2:                                        ; preds = %if.end.1
  %add.2 = fadd float %4, %5
  br label %if.end.2

if.end.2:                                         ; preds = %if.then.2, %if.else.2
  %x.0.2 = phi float [ %add.2, %if.then.2 ], [ %sub.2, %if.else.2 ]
  store float %x.0.2, float* getelementptr inbounds ([4 x float], [4 x float]* @c, i64 0, i64 2), align 4, !tbaa !3
  %6 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 3), align 4, !tbaa !3
  %7 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @b, i64 0, i64 3), align 4, !tbaa !3
  %cmp3.3 = fcmp olt float %6, %7
  br i1 %cmp3.3, label %if.then.3, label %if.else.3

if.else.3:                                        ; preds = %if.end.2
  %sub.3 = fsub float %6, %7
  br label %if.end.3

if.then.3:                                        ; preds = %if.end.2
  %add.3 = fadd float %6, %7
  br label %if.end.3

if.end.3:                                         ; preds = %if.then.3, %if.else.3
  %x.0.3 = phi float [ %add.3, %if.then.3 ], [ %sub.3, %if.else.3 ]
  store float %x.0.3, float* getelementptr inbounds ([4 x float], [4 x float]* @c, i64 0, i64 3), align 4, !tbaa !3
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
!4 = !{!"float", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
