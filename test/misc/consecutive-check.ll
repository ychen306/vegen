; RUN: %opt -gslp %s -o /dev/null

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

%struct.sqlite3PrngType = type { i8, i8, i8, [256 x i8] }

@sqlite3Prng = external dso_local unnamed_addr global %struct.sqlite3PrngType, align 1

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #0

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #0

define internal fastcc void @sqlite3Randomness(i32 %N) unnamed_addr {
while.body.lr.ph:
  br i1 undef, label %while.body.us.preheader, label %while.body.preheader

while.body.us.preheader:                          ; preds = %while.body.lr.ph
  br label %while.body.us

while.body.preheader:                             ; preds = %while.body.lr.ph
  %.pre = load i8, i8* getelementptr inbounds (%struct.sqlite3PrngType, %struct.sqlite3PrngType* @sqlite3Prng, i64 0, i32 1), align 1, !tbaa !0
  br label %while.body

while.body.us:                                    ; preds = %randomByte.exit.us, %while.body.us.preheader
  %N.addr.03.us = phi i32 [ %dec.us, %randomByte.exit.us ], [ %N, %while.body.us.preheader ]
  %dec.us = add nsw i32 %N.addr.03.us, -1
  br label %entry.if.end_crit_edge.i.us

entry.if.end_crit_edge.i.us:                      ; preds = %while.body.us
  %.pre.i.us = load i8, i8* getelementptr inbounds (%struct.sqlite3PrngType, %struct.sqlite3PrngType* @sqlite3Prng, i64 0, i32 2), align 1, !tbaa !4
  br label %randomByte.exit.us

randomByte.exit.us:                               ; preds = %entry.if.end_crit_edge.i.us
  %tobool.not.us = icmp eq i32 %dec.us, 0
  br i1 %tobool.not.us, label %while.end.loopexit, label %while.body.us, !llvm.loop !5

while.body:                                       ; preds = %while.body, %while.body.preheader
  %0 = phi i8 [ %inc26.i, %while.body ], [ %.pre, %while.body.preheader ]
  %N.addr.03 = phi i32 [ %dec, %while.body ], [ %N, %while.body.preheader ]
  %dec = add nsw i32 %N.addr.03, -1
  %inc26.i = add i8 %0, 1
  %idxprom27.i = zext i8 %inc26.i to i64
  %arrayidx28.i = getelementptr inbounds %struct.sqlite3PrngType, %struct.sqlite3PrngType* @sqlite3Prng, i64 0, i32 3, i64 %idxprom27.i
  %1 = load i8, i8* %arrayidx28.i, align 1, !tbaa !8
  %tobool.not = icmp eq i32 %dec, 0
  br i1 %tobool.not, label %while.end.loopexit7, label %while.body, !llvm.loop !9

while.end.loopexit7:                              ; preds = %while.body
  ret void

while.end.loopexit:                               ; preds = %randomByte.exit.us
  ret void
}

attributes #0 = { argmemonly nofree nosync nounwind willreturn }

!0 = !{!1, !2, i64 1}
!1 = !{!"sqlite3PrngType", !2, i64 0, !2, i64 1, !2, i64 2, !2, i64 3}
!2 = !{!"omnipotent char", !3, i64 0}
!3 = !{!"Simple C/C++ TBAA"}
!4 = !{!1, !2, i64 2}
!5 = distinct !{!5, !6, !7}
!6 = !{!"llvm.loop.mustprogress"}
!7 = !{!"llvm.loop.unswitch.partial.disable"}
!8 = !{!2, !2, i64 0}
!9 = distinct !{!9, !6}
