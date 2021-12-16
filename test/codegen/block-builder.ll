; RUN: %opt -gslp -test-codegen %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define dso_local void @_Z15raytrace_serialiiiiPfS_S_PiPK13LinearBVHNodePK8Triangle() local_unnamed_addr {
for.cond5.preheader.lr.ph:
  br label %for.cond5.preheader

for.cond5.preheader:                              ; preds = %for.cond.cleanup7, %for.cond5.preheader.lr.ph
  br i1 undef, label %for.body8.lr.ph, label %for.cond.cleanup7

for.body8.lr.ph:                                  ; preds = %for.cond5.preheader
  br label %for.body8

for.cond.cleanup:                                 ; preds = %for.cond.cleanup7
  ret void

for.cond.cleanup7:                                ; preds = %_ZL12BVHIntersectPK13LinearBVHNodePK8TriangleR3Ray.exit, %for.cond5.preheader
  br i1 undef, label %for.cond.cleanup, label %for.cond5.preheader, !llvm.loop !0

for.body8:                                        ; preds = %_ZL12BVHIntersectPK13LinearBVHNodePK8TriangleR3Ray.exit, %for.body8.lr.ph
  br label %while.cond.i.outer

while.cond.i.outer:                               ; preds = %for.body8
  br label %while.cond.i

while.cond.i:                                     ; preds = %while.cond.i.outer
  br i1 undef, label %if.else22.i, label %if.then.i

if.then.i:                                        ; preds = %while.cond.i
  %cmp.not.i = icmp eq i8 undef, 0
  br i1 %cmp.not.i, label %if.else.i, label %for.body.preheader.i

for.body.preheader.i:                             ; preds = %if.then.i
  br label %for.body.i

for.cond.cleanup.i:                               ; preds = %_Z12TriIntersectRK8TriangleR3Ray.exit.thread.i
  br label %_ZL12BVHIntersectPK13LinearBVHNodePK8TriangleR3Ray.exit

for.body.i:                                       ; preds = %_Z12TriIntersectRK8TriangleR3Ray.exit.thread.i, %for.body.preheader.i
  br i1 undef, label %_Z12TriIntersectRK8TriangleR3Ray.exit.thread.i, label %if.end.i.i

if.end.i.i:                                       ; preds = %for.body.i
  br i1 undef, label %_Z12TriIntersectRK8TriangleR3Ray.exit.thread.i, label %if.end37.i.i

if.end37.i.i:                                     ; preds = %if.end.i.i
  br i1 undef, label %_Z12TriIntersectRK8TriangleR3Ray.exit.thread.i, label %if.end48.i.i

if.end48.i.i:                                     ; preds = %if.end37.i.i
  br i1 undef, label %_Z12TriIntersectRK8TriangleR3Ray.exit.thread.i, label %0

0:                                                ; preds = %if.end48.i.i
  br label %_Z12TriIntersectRK8TriangleR3Ray.exit.thread.i

_Z12TriIntersectRK8TriangleR3Ray.exit.thread.i:   ; preds = %0, %if.end48.i.i, %if.end37.i.i, %if.end.i.i, %for.body.i
  br i1 undef, label %for.cond.cleanup.i, label %for.body.i, !llvm.loop !2

if.else.i:                                        ; preds = %if.then.i
  %add17.i = add nsw i32 0, 1
  ret void

if.else22.i:                                      ; preds = %while.cond.i
  br label %_ZL12BVHIntersectPK13LinearBVHNodePK8TriangleR3Ray.exit

_ZL12BVHIntersectPK13LinearBVHNodePK8TriangleR3Ray.exit: ; preds = %if.else22.i, %for.cond.cleanup.i
  %ray.sroa.17.6.ph.i = phi float [ 0x46293E5940000000, %if.else22.i ], [ undef, %for.cond.cleanup.i ]
  %ray.sroa.21.6.ph.i = phi i32 [ 0, %if.else22.i ], [ undef, %for.cond.cleanup.i ]
  br i1 undef, label %for.cond.cleanup7, label %for.body8, !llvm.loop !3
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
!2 = distinct !{!2, !1}
!3 = distinct !{!3, !1}
