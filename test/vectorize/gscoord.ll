; RUN: %opt -gslp %s -o /dev/null

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

%struct.anon = type { %struct.g }
%struct.g = type { float, i64, float, i32, i32 }

@h = dso_local local_unnamed_addr global %struct.anon* null, align 8

; Function Attrs: nofree norecurse nounwind ssp uwtable willreturn
define dso_local i32 @i() local_unnamed_addr #0 {
entry:
  %0 = load %struct.anon*, %struct.anon** @h, align 8, !tbaa !3
  %b = getelementptr inbounds %struct.anon, %struct.anon* %0, i64 0, i32 0, i32 0
  %1 = load float, float* %b, align 8, !tbaa !7
  %mul = fmul float %1, 0.000000e+00
  %conv = fptosi float %mul to i32
  %e = getelementptr inbounds %struct.anon, %struct.anon* %0, i64 0, i32 0, i32 3
  store i32 %conv, i32* %e, align 4, !tbaa !13
  %d = getelementptr inbounds %struct.anon, %struct.anon* %0, i64 0, i32 0, i32 2
  %2 = load float, float* %d, align 8, !tbaa !14
  %mul3 = fmul float %2, 0.000000e+00
  %conv4 = fptosi float %mul3 to i32
  %f = getelementptr inbounds %struct.anon, %struct.anon* %0, i64 0, i32 0, i32 4
  store i32 %conv4, i32* %f, align 8, !tbaa !15
  ret i32 undef
}

attributes #0 = { nofree norecurse nounwind ssp uwtable willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"any pointer", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = !{!8, !10, i64 0}
!8 = !{!"", !9, i64 0}
!9 = !{!"", !10, i64 0, !11, i64 8, !10, i64 16, !12, i64 20, !12, i64 24}
!10 = !{!"float", !5, i64 0}
!11 = !{!"long", !5, i64 0}
!12 = !{!"int", !5, i64 0}
!13 = !{!8, !12, i64 20}
!14 = !{!8, !10, i64 16}
!15 = !{!8, !12, i64 24}
