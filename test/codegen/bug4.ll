; RUN: %opt -gslp -test-codegen %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

@c = dso_local local_unnamed_addr global i16 0, align 2
@b = dso_local local_unnamed_addr global i16 0, align 2
@a = dso_local local_unnamed_addr global i8 0, align 1
@d = dso_local local_unnamed_addr global i32 0, align 4

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @e() local_unnamed_addr #0 {
entry:
  %0 = load i16, i16* @c, align 2, !tbaa !3
  %tobool.not = icmp eq i16 %0, 0
  br i1 %tobool.not, label %for.cond.preheader, label %if.end

for.cond.preheader:                               ; preds = %entry
  %1 = load i16, i16* @b, align 2, !tbaa !3
  %tobool1.not = icmp eq i16 %1, 0
  br i1 %tobool1.not, label %for.cond.us.preheader, label %for.cond.preheader1

for.cond.preheader1:                              ; preds = %for.cond.preheader
  br label %for.cond

for.cond.us.preheader:                            ; preds = %for.cond.preheader
  br label %for.cond.us

for.cond.us:                                      ; preds = %for.cond.us.preheader, %for.cond.us
  br label %for.cond.us

for.cond:                                         ; preds = %for.cond.preheader1, %for.cond
  br label %for.cond

if.end:                                           ; preds = %entry
  ret void
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { norecurse nounwind readnone ssp uwtable willreturn "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"short", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
