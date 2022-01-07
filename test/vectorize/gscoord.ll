; RUN: %opt -gslp %s -o /dev/null

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

%struct.anon = type { %struct.g }
%struct.g = type { float, i64, float, i32, i32 }

@h = external dso_local local_unnamed_addr global %struct.anon*, align 8

define dso_local void @i() local_unnamed_addr {
entry:
  %0 = load %struct.anon*, %struct.anon** @h, align 8, !tbaa !0
  %b = getelementptr inbounds %struct.anon, %struct.anon* %0, i64 0, i32 0, i32 0
  %1 = load float, float* %b, align 8, !tbaa !4
  %mul = fmul float %1, 0.000000e+00
  %conv = fptosi float %mul to i32
  %e = getelementptr inbounds %struct.anon, %struct.anon* %0, i64 0, i32 0, i32 3
  store i32 %conv, i32* %e, align 4, !tbaa !10
  %d = getelementptr inbounds %struct.anon, %struct.anon* %0, i64 0, i32 0, i32 2
  %2 = load float, float* %d, align 8, !tbaa !11
  %mul3 = fmul float %2, 0.000000e+00
  %conv4 = fptosi float %mul3 to i32
  %f = getelementptr inbounds %struct.anon, %struct.anon* %0, i64 0, i32 0, i32 4
  store i32 %conv4, i32* %f, align 8, !tbaa !12
  ret void
}

!0 = !{!1, !1, i64 0}
!1 = !{!"any pointer", !2, i64 0}
!2 = !{!"omnipotent char", !3, i64 0}
!3 = !{!"Simple C/C++ TBAA"}
!4 = !{!5, !7, i64 0}
!5 = !{!"", !6, i64 0}
!6 = !{!"", !7, i64 0, !8, i64 8, !7, i64 16, !9, i64 20, !9, i64 24}
!7 = !{!"float", !2, i64 0}
!8 = !{!"long", !2, i64 0}
!9 = !{!"int", !2, i64 0}
!10 = !{!5, !9, i64 20}
!11 = !{!5, !7, i64 16}
!12 = !{!5, !9, i64 24}
