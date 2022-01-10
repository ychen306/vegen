; RUN: %opt -gslp -no-unroll %s -o /dev/null

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

%struct.j = type { %struct.ae, %struct.ae, %struct.f, i32 }
%struct.ae = type { %struct.f, %struct.f }
%struct.f = type { i32, i32 }

define dso_local i32 @p() local_unnamed_addr {
entry:
  br i1 zeroinitializer, label %while.end, label %while.body.lr.ph

while.body.lr.ph:                                 ; preds = %entry
  %c.i = getelementptr inbounds %struct.j, %struct.j* zeroinitializer, i64 0, i32 2, i32 0
  %c1.i = getelementptr inbounds %struct.j, %struct.j* zeroinitializer, i64 0, i32 1, i32 1, i32 0
  %d.i = getelementptr inbounds %struct.j, %struct.j* zeroinitializer, i64 0, i32 2, i32 1
  %d5.i = getelementptr inbounds %struct.j, %struct.j* zeroinitializer, i64 0, i32 1, i32 1, i32 1
  br label %while.body

while.body:                                       ; preds = %cond.end15, %while.body.lr.ph
  br i1 zeroinitializer, label %if.else, label %if.then

if.then:                                          ; preds = %while.body
  br label %if.end5

if.else:                                          ; preds = %while.body
  br label %if.end5

if.end5:                                          ; preds = %if.else, %if.then
  %tobool9.not = phi i1 [ true, %if.then ], [ false, %if.else ]
  br i1 %tobool9.not, label %cond.true12, label %cond.end15

cond.true12:                                      ; preds = %if.end5
  %0 = load i32, i32* %c.i, align 8, !tbaa !0
  store i32 %0, i32* %c1.i, align 8, !tbaa !7
  %1 = load i32, i32* %d.i, align 4, !tbaa !8
  store i32 %1, i32* %d5.i, align 4, !tbaa !9
  br label %cond.end15

cond.end15:                                       ; preds = %cond.true12, %if.end5
  br i1 zeroinitializer, label %while.end, label %while.body, !llvm.loop !10

while.end:                                        ; preds = %cond.end15, %entry
  ret i32 zeroinitializer
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #0

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #0

attributes #0 = { argmemonly nofree nosync nounwind willreturn }

!0 = !{!1, !4, i64 32}
!1 = !{!"", !2, i64 0, !2, i64 16, !3, i64 32, !4, i64 40}
!2 = !{!"", !3, i64 0, !3, i64 8}
!3 = !{!"", !4, i64 0, !4, i64 4}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = !{!1, !4, i64 24}
!8 = !{!1, !4, i64 36}
!9 = !{!1, !4, i64 28}
!10 = distinct !{!10, !11}
!11 = !{!"llvm.loop.mustprogress"}
