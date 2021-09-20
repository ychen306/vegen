; RUN: %opt %s -gslp -o /dev/null

; ModuleID = 'x.ll'
source_filename = "/Users/tom/workspace/test-suite/MultiSource/Benchmarks/DOE-ProxyApps-C/miniGMG/operators.ompif.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #0

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #0

define dso_local void @exchange_boundary() local_unnamed_addr {
entry:
  %exchange = alloca [27 x i32], align 16
  br label %for.body.us.preheader

for.body.us.preheader:                            ; preds = %entry
  br label %for.body.us

for.body.us:                                      ; preds = %for.inc.us, %for.body.us.preheader
  %indvars.iv129 = phi i64 [ %indvars.iv.next130, %for.inc.us ], [ 0, %for.body.us.preheader ]
  br i1 undef, label %if.end10.us, label %if.then4.us

if.then4.us:                                      ; preds = %for.body.us
  %0 = load i32, i32* undef, align 4, !tbaa !0
  %arrayidx8.us = getelementptr inbounds [27 x i32], [27 x i32]* %exchange, i64 0, i64 %indvars.iv129
  %1 = load i32, i32* %arrayidx8.us, align 4, !tbaa !0
  %or9.us = or i32 %1, %0
  store i32 %or9.us, i32* %arrayidx8.us, align 4, !tbaa !0
  br label %if.end10.us

if.end10.us:                                      ; preds = %if.then4.us, %for.body.us
  br label %for.inc.us

for.inc.us:                                       ; preds = %if.end10.us
  %indvars.iv.next130 = add nuw nsw i64 %indvars.iv129, 1
  br i1 undef, label %for.end.loopexit, label %for.body.us, !llvm.loop !4

for.end.loopexit:                                 ; preds = %for.inc.us
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i1 immarg) #1

attributes #0 = { argmemonly nofree nosync nounwind willreturn }
attributes #1 = { argmemonly nofree nosync nounwind willreturn writeonly }

!0 = !{!1, !1, i64 0}
!1 = !{!"int", !2, i64 0}
!2 = !{!"omnipotent char", !3, i64 0}
!3 = !{!"Simple C/C++ TBAA"}
!4 = distinct !{!4, !5, !6}
!5 = !{!"llvm.loop.mustprogress"}
!6 = !{!"llvm.loop.unroll.disable"}
