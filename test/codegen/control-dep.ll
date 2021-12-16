; RUN: %opt -gslp -test-codegen %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define dso_local void @_Z15raytrace_serialiiiiPfS_S_PiPK13LinearBVHNodePK8Triangle() local_unnamed_addr {
for.cond5.preheader.lr.ph:
  br i1 undef, label %for.cond.cleanup, label %for.cond.cleanup7

for.cond.cleanup:                                 ; preds = %for.cond5.preheader.lr.ph, %for.cond.cleanup7
  ret void

for.cond.cleanup7:                                ; preds = %for.cond.cleanup7, %for.cond5.preheader.lr.ph
  %.pr = phi i1 [ undef, %for.cond.cleanup7 ], [ false, %for.cond5.preheader.lr.ph ]
  br i1 %.pr, label %for.cond.cleanup, label %for.cond.cleanup7, !llvm.loop !0
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #0

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #0

; Function Attrs: inaccessiblememonly nofree nosync nounwind willreturn
declare void @llvm.experimental.noalias.scope.decl(metadata) #1

attributes #0 = { argmemonly nofree nosync nounwind willreturn }
attributes #1 = { inaccessiblememonly nofree nosync nounwind willreturn }

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}
