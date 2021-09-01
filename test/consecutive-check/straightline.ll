; RUN: %opt -test-consecutive-check %s -o /dev/null 2>&1 | FileCheck %s

; CHECK-DAG: load i32, i32* %b{{.*}}load i32, i32* %arrayidx2{{.*}} are consecutive
; CHECK-DAG: store i32 %0, i32* %a{{.*}}store i32 %1, i32* %arrayidx3{{.*}} are consecutive

; Function Attrs: nofree norecurse nounwind ssp uwtable willreturn
define dso_local void @foo(i32* nocapture %a, i32* nocapture readonly %b) local_unnamed_addr #0 {
entry:
  %0 = load i32, i32* %b, align 4, !tbaa !3
  store i32 %0, i32* %a, align 4, !tbaa !3
  %arrayidx2 = getelementptr inbounds i32, i32* %b, i64 1
  %1 = load i32, i32* %arrayidx2, align 4, !tbaa !3
  %arrayidx3 = getelementptr inbounds i32, i32* %a, i64 1
  store i32 %1, i32* %arrayidx3, align 4, !tbaa !3
  ret void
}

attributes #0 = { nofree norecurse nounwind ssp uwtable willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
