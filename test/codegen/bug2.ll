; RUN: %opt -gslp -test-codegen %s

source_filename = "small.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@a = dso_local local_unnamed_addr global i32 0, align 4
@b = dso_local local_unnamed_addr global i16 0, align 2

; Function Attrs: norecurse nounwind readonly ssp uwtable
define dso_local void @c() local_unnamed_addr #0 {
entry:
  %0 = load i32, i32* @a, align 4, !tbaa !3
  %tobool.not = icmp eq i32 %0, 0
  br i1 %tobool.not, label %if.end4, label %for.condthread-pre-split

for.condthread-pre-split:                         ; preds = %entry
  %.pr = load i16, i16* @b, align 2, !tbaa !7
  %phi.cmp = icmp eq i16 %.pr, 0
  br i1 %phi.cmp, label %for.cond.preheader, label %for.cond3.preheader

for.cond3.preheader:                              ; preds = %for.condthread-pre-split
  br label %for.cond3

for.cond.preheader:                               ; preds = %for.condthread-pre-split
  br label %for.cond

for.cond:                                         ; preds = %for.cond.preheader, %for.cond
  br label %for.cond

for.cond3:                                        ; preds = %for.cond3.preheader, %for.cond3
  br label %for.cond3

if.end4:                                          ; preds = %entry
  ret void
}

; Function Attrs: norecurse nounwind readnone ssp uwtable willreturn
define dso_local i32 @main() local_unnamed_addr #1 {
entry:
  ret i32 0
}

attributes #0 = { norecurse nounwind readonly ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { norecurse nounwind readnone ssp uwtable willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = !{!8, !8, i64 0}
!8 = !{!"short", !5, i64 0}
