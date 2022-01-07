; RUN: %opt -gslp -adce %s -o /dev/null

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

%struct.point = type { i32, i32 }

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @get_x(%struct.point* nocapture readonly %pts, i32* noalias nocapture %x) local_unnamed_addr #0 {
entry:
  %x1 = getelementptr inbounds %struct.point, %struct.point* %pts, i64 0, i32 0
  %0 = load i32, i32* %x1, align 4, !tbaa !3
  store i32 %0, i32* %x, align 4, !tbaa !8
  %x1.1 = getelementptr inbounds %struct.point, %struct.point* %pts, i64 1, i32 1
  %1 = load i32, i32* %x1.1, align 4, !tbaa !3
  %arrayidx3.1 = getelementptr inbounds i32, i32* %x, i64 1
  store i32 %1, i32* %arrayidx3.1, align 4, !tbaa !8
  %x1.2 = getelementptr inbounds %struct.point, %struct.point* %pts, i64 2, i32 0
  %2 = load i32, i32* %x1.2, align 4, !tbaa !3
  %arrayidx3.2 = getelementptr inbounds i32, i32* %x, i64 2
  store i32 %2, i32* %arrayidx3.2, align 4, !tbaa !8
  %x1.3 = getelementptr inbounds %struct.point, %struct.point* %pts, i64 3, i32 1
  %3 = load i32, i32* %x1.3, align 4, !tbaa !3
  %arrayidx3.3 = getelementptr inbounds i32, i32* %x, i64 3
  store i32 %3, i32* %arrayidx3.3, align 4, !tbaa !8
  ret void
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="icelake-client" "target-features"="+64bit,+adx,+aes,+avx,+avx2,+avx512bitalg,+avx512bw,+avx512cd,+avx512dq,+avx512f,+avx512ifma,+avx512vbmi,+avx512vbmi2,+avx512vl,+avx512vnni,+avx512vpopcntdq,+bmi,+bmi2,+clflushopt,+cmov,+cx16,+cx8,+f16c,+fma,+fsgsbase,+fxsr,+gfni,+invpcid,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+prfchw,+rdpid,+rdrnd,+rdseed,+sahf,+sgx,+sha,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+vaes,+vpclmulqdq,+x87,+xsave,+xsavec,+xsaveopt,+xsaves,-amx-bf16,-amx-int8,-amx-tile,-avx512bf16,-avx512er,-avx512pf,-avx512vp2intersect,-avxvnni,-cldemote,-clwb,-clzero,-enqcmd,-fma4,-hreset,-kl,-lwp,-movdir64b,-movdiri,-mwaitx,-pconfig,-pku,-prefetchwt1,-ptwrite,-rtm,-serialize,-shstk,-sse4a,-tbm,-tsxldtrk,-uintr,-waitpkg,-wbnoinvd,-widekl,-xop" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !5, i64 0}
!4 = !{!"point", !5, i64 0, !5, i64 4}
!5 = !{!"int", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C/C++ TBAA"}
!8 = !{!5, !5, i64 0}
