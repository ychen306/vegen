; RUN: %opt -gslp %s -S | FileCheck %s

; CHECK: call{{.*}}llvm.masked.gather

source_filename = "gather.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable willreturn
define dso_local void @foo(i32** nocapture readonly %ptrs, i32* nocapture %dst) local_unnamed_addr #0 {
entry:
  %0 = load i32*, i32** %ptrs, align 8, !tbaa !3
  %1 = load i32, i32* %0, align 4, !tbaa !7
  %arrayidx1 = getelementptr inbounds i32*, i32** %ptrs, i64 1
  %2 = load i32*, i32** %arrayidx1, align 8, !tbaa !3
  %3 = load i32, i32* %2, align 4, !tbaa !7
  %arrayidx2 = getelementptr inbounds i32*, i32** %ptrs, i64 2
  %4 = load i32*, i32** %arrayidx2, align 8, !tbaa !3
  %5 = load i32, i32* %4, align 4, !tbaa !7
  %arrayidx3 = getelementptr inbounds i32*, i32** %ptrs, i64 3
  %6 = load i32*, i32** %arrayidx3, align 8, !tbaa !3
  %7 = load i32, i32* %6, align 4, !tbaa !7
  store i32 %1, i32* %dst, align 4, !tbaa !7
  %arrayidx5 = getelementptr inbounds i32, i32* %dst, i64 1
  store i32 %3, i32* %arrayidx5, align 4, !tbaa !7
  %arrayidx6 = getelementptr inbounds i32, i32* %dst, i64 2
  store i32 %5, i32* %arrayidx6, align 4, !tbaa !7
  %arrayidx7 = getelementptr inbounds i32, i32* %dst, i64 3
  store i32 %7, i32* %arrayidx7, align 4, !tbaa !7
  ret void
}

attributes #0 = { nofree norecurse nounwind ssp uwtable willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="icelake-client" "target-features"="+64bit,+adx,+aes,+avx,+avx2,+avx512bitalg,+avx512bw,+avx512cd,+avx512dq,+avx512f,+avx512ifma,+avx512vbmi,+avx512vbmi2,+avx512vl,+avx512vnni,+avx512vpopcntdq,+bmi,+bmi2,+clflushopt,+cmov,+cx16,+cx8,+f16c,+fma,+fsgsbase,+fxsr,+gfni,+invpcid,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+prfchw,+rdpid,+rdrnd,+rdseed,+sahf,+sgx,+sha,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+vaes,+vpclmulqdq,+x87,+xsave,+xsavec,+xsaveopt,+xsaves,-amx-bf16,-amx-int8,-amx-tile,-avx512bf16,-avx512er,-avx512pf,-avx512vp2intersect,-avxvnni,-cldemote,-clwb,-clzero,-enqcmd,-fma4,-hreset,-kl,-lwp,-movdir64b,-movdiri,-mwaitx,-pconfig,-pku,-prefetchwt1,-ptwrite,-rtm,-serialize,-shstk,-sse4a,-tbm,-tsxldtrk,-uintr,-waitpkg,-wbnoinvd,-widekl,-xop" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"any pointer", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = !{!8, !8, i64 0}
!8 = !{!"int", !5, i64 0}
