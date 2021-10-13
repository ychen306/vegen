; RUN: %opt -gslp %s -S | FileCheck %s

; CHECK:  %0 = load <4 x float>, <4 x float>* bitcast ([4 x float]* @a to <4 x float>*)
; CHECK-NEXT:  %1 = load <4 x float>, <4 x float>* bitcast ([4 x float]* @b to <4 x float>*)
; CHECK-NEXT:  %2 = fcmp olt <4 x float> %0, %1
; CHECK-NEXT:  %3 = fadd <4 x float> %0, %1
; CHECK-NEXT:  call void @llvm.masked.store.v4f32.p0v4f32(<4 x float> %3, <4 x float>* bitcast ([4 x float]* @c to <4 x float>*), i32 16, <4 x i1> %2)
; CHECK-NEXT:  ret void

source_filename = "cond.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@a = dso_local local_unnamed_addr global [4 x float] zeroinitializer, align 16
@b = dso_local local_unnamed_addr global [4 x float] zeroinitializer, align 16
@c = dso_local local_unnamed_addr global [4 x float] zeroinitializer, align 16

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo() local_unnamed_addr #0 {
entry:
  %0 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 0), align 16, !tbaa !3
  %1 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @b, i64 0, i64 0), align 16, !tbaa !3
  %cmp3 = fcmp olt float %0, %1
  br i1 %cmp3, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %add = fadd float %0, %1
  store float %add, float* getelementptr inbounds ([4 x float], [4 x float]* @c, i64 0, i64 0), align 16, !tbaa !3
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %2 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 1), align 4, !tbaa !3
  %3 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @b, i64 0, i64 1), align 4, !tbaa !3
  %cmp3.1 = fcmp olt float %2, %3
  br i1 %cmp3.1, label %if.then.1, label %if.end.1

if.then.1:                                        ; preds = %if.end
  %add.1 = fadd float %2, %3
  store float %add.1, float* getelementptr inbounds ([4 x float], [4 x float]* @c, i64 0, i64 1), align 4, !tbaa !3
  br label %if.end.1

if.end.1:                                         ; preds = %if.then.1, %if.end
  %4 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 2), align 8, !tbaa !3
  %5 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @b, i64 0, i64 2), align 8, !tbaa !3
  %cmp3.2 = fcmp olt float %4, %5
  br i1 %cmp3.2, label %if.then.2, label %if.end.2

if.then.2:                                        ; preds = %if.end.1
  %add.2 = fadd float %4, %5
  store float %add.2, float* getelementptr inbounds ([4 x float], [4 x float]* @c, i64 0, i64 2), align 8, !tbaa !3
  br label %if.end.2

if.end.2:                                         ; preds = %if.then.2, %if.end.1
  %6 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @a, i64 0, i64 3), align 4, !tbaa !3
  %7 = load float, float* getelementptr inbounds ([4 x float], [4 x float]* @b, i64 0, i64 3), align 4, !tbaa !3
  %cmp3.3 = fcmp olt float %6, %7
  br i1 %cmp3.3, label %if.then.3, label %if.end.3

if.then.3:                                        ; preds = %if.end.2
  %add.3 = fadd float %6, %7
  store float %add.3, float* getelementptr inbounds ([4 x float], [4 x float]* @c, i64 0, i64 3), align 4, !tbaa !3
  br label %if.end.3

if.end.3:                                         ; preds = %if.then.3, %if.end.2
  ret void
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="icelake-client" "target-features"="+64bit,+adx,+aes,+avx,+avx2,+avx512bitalg,+avx512bw,+avx512cd,+avx512dq,+avx512f,+avx512ifma,+avx512vbmi,+avx512vbmi2,+avx512vl,+avx512vnni,+avx512vpopcntdq,+bmi,+bmi2,+clflushopt,+cmov,+cx16,+cx8,+f16c,+fma,+fsgsbase,+fxsr,+gfni,+invpcid,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+prfchw,+rdpid,+rdrnd,+rdseed,+sahf,+sgx,+sha,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+vaes,+vpclmulqdq,+x87,+xsave,+xsavec,+xsaveopt,+xsaves,-amx-bf16,-amx-int8,-amx-tile,-avx512bf16,-avx512er,-avx512pf,-avx512vp2intersect,-avxvnni,-cldemote,-clwb,-clzero,-enqcmd,-fma4,-hreset,-kl,-lwp,-movdir64b,-movdiri,-mwaitx,-pconfig,-pku,-prefetchwt1,-ptwrite,-rtm,-serialize,-shstk,-sse4a,-tbm,-tsxldtrk,-uintr,-waitpkg,-wbnoinvd,-widekl,-xop" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"float", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
