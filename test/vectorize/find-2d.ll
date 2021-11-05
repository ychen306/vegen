; RUN: %opt -gslp -adce -no-unroll %s -S | FileCheck %s

; CHECK:  [[N_GT_0:%.*]] = icmp sgt i32 %n, 0
; CHECK-NEXT:  [[BIG_N2:%.*]] = sext i32 %n to i64
; CHECK-NEXT:  [[BIG_N:%.*]] = sext i32 %n to i64
; CHECK-NEXT:  [[NEEDLES_ADDR:%.*]] = bitcast i32* %needles to <4 x i32>*
; CHECK-NEXT:  [[NEEDLES:%.*]] = load <4 x i32>, <4 x i32>* [[NEEDLES_ADDR]]
; CHECK-NEXT:  br i1 [[N_GT_0]], label %[[PREHEADER:.*]], label %[[SKIP_LOOP:.*]]

; CHECK: [[PREHEADER]]:
; CHECK-NOT: br
; CHECK:  [[N_SPLAT:%.*]] = zext <4 x i32> {{%.*}} to <4 x i64>
; CHECK-NEXT:  br label %[[HEADER:.*]]

; CHECK:[[SKIP_LOOP]]:
; CHECK-NEXT:  br label %[[DONE:.*]]

; CHECK:[[HEADER]]:
; CHECK-NEXT:  [[FOUND_OUT:%.*]] = phi <4 x i1> [ undef, %[[PREHEADER]] ], [ [[FOUND_OUT_NEXT:%.*]], %[[LATCH:.*]] ]
; CHECK-NEXT:  [[IDX_OUT:%.*]] = phi <4 x i32> [ undef, %[[PREHEADER]] ], [ [[IDX_OUT_NEXT:%.*]], %[[LATCH]] ]
; CHECK-NEXT:  [[IDX:%.*]] = phi <4 x i32> [ undef, %[[PREHEADER]] ], [ [[IDX_OUT_INNER_NEXT:%.*]], %[[LATCH]] ]
; CHECK-NEXT:  [[J:%.*]] = phi <4 x i64> [ zeroinitializer, %[[PREHEADER]] ], [ [[J_NEXT:%.*]], %[[LATCH]] ]
; CHECK-NEXT:  [[ACTIVE_OUTER:%.*]] = phi <4 x i1> [ <i1 true, i1 true, i1 true, i1 true>, %[[PREHEADER]] ], [ [[ACTIVE_OUTER_NEXT:%.*]], %[[LATCH]] ]
; CHECK-NEXT:  [[TMP0:%.*]] = insertelement <4 x i64> undef, i64 [[BIG_N]], i64 0
; CHECK-NEXT:  [[TMP1:%.*]] = insertelement <4 x i64> [[TMP0]], i64 [[BIG_N]], i64 1
; CHECK-NEXT:  [[TMP2:%.*]] = insertelement <4 x i64> [[TMP1]], i64 [[BIG_N]], i64 2
; CHECK-NEXT:  [[BIG_N_SPLAT:%.*]] = insertelement <4 x i64> [[TMP2]], i64 [[BIG_N]], i64 3
; CHECK-NEXT:  [[J_X_N:%.*]] = mul <4 x i64> [[J:%.*]], [[BIG_N_SPLAT]]
; CHECK-NEXT:  [[TMP3:%.*]] = insertelement <4 x i1> undef, i1 [[N_GT_0]], i64 0
; CHECK-NEXT:  [[TMP4:%.*]] = insertelement <4 x i1> [[TMP3]], i1 [[N_GT_0]], i64 1
; CHECK-NEXT:  [[TMP5:%.*]] = insertelement <4 x i1> [[TMP4]], i1 [[N_GT_0]], i64 2
; CHECK-NEXT:  [[N_GT_0_SPLAT:%.*]] = insertelement <4 x i1> [[TMP5]], i1 [[N_GT_0]], i64 3
; CHECK-NEXT:  [[ACTIVE_INNER_INIT:%.*]] = and <4 x i1> [[ACTIVE_OUTER]], [[N_GT_0_SPLAT]]
; CHECK-NEXT:  br label %[[HEADER_INNER:.*]]

; CHECK:[[LATCH]]:
; CHECK-NEXT:  [[J_NOT_DONE:%.*]] = xor <4 x i1> [[J_DONE:%.*]], <i1 true, i1 true, i1 true, i1 true>
; CHECK-NEXT:  [[TMP6:%.*]] = and <4 x i1> [[IDX_EQ_NEG:%.*]], [[J_NOT_DONE]]
; CHECK-NEXT:  [[ACTIVE_OUTER_NEXT]] = and <4 x i1> [[ACTIVE_OUTER]], [[TMP6]]
; CHECK-NEXT:  [[ANY_OUTER_ACTIVE:%.*]] = call i1 @llvm.vector.reduce.or.v4i1(<4 x i1> [[ACTIVE_OUTER_NEXT]])
; CHECK-NEXT:  br i1 [[ANY_OUTER_ACTIVE]], label %[[HEADER]], label %[[EXIT:.*]]

; CHECK:[[EXIT]]:
; CHECK-NEXT:  [[NOT_FOUND:%.*]] = xor <4 x i1> [[FOUND_OUT_NEXT]], <i1 true, i1 true, i1 true, i1 true>
; CHECK-NEXT:  [[IDX_LOOP_OUT:%.*]] = select <4 x i1> [[NOT_FOUND]], <4 x i32> [[IDX_OUT_NEXT]], <4 x i32> <i32 -1, i32 -1, i32 -1, i32 -1>
; CHECK-NEXT:  br label %[[DONE]]

; CHECK:[[HEADER_INNER]]:
; CHECK-NEXT:  [[IDX_OUT_INNER:%.*]] = phi <4 x i32> [ [[IDX]], %[[HEADER]] ], [ [[IDX_OUT_INNER_NEXT]], %[[LATCH_INNER:.*]] ]
; CHECK-NEXT:  [[IDX_INNER:%.*]] = phi <4 x i32> [ <i32 -1, i32 -1, i32 -1, i32 -1>, %[[HEADER]] ], [ [[IDX_INNER_NEXT:%.*]], %[[LATCH_INNER]] ]
; CHECK-NEXT:  [[K:%.*]] = phi <4 x i64> [ zeroinitializer, %[[HEADER]] ], [ [[K_NEXT:%.*]], %[[LATCH_INNER]] ]
; CHECK-NEXT:  [[ACTIVE_INNER:%.*]] = phi <4 x i1> [ [[ACTIVE_INNER_INIT]], %[[HEADER]] ], [ [[ACTIVE_INNER_NEXT:%.*]], %[[LATCH_INNER]] ]
; CHECK-NEXT:  [[II:%.*]] = add <4 x i64> [[K]], [[J_X_N]]
; CHECK-NEXT:  [[A_ADDR:%.*]] = getelementptr i32, i32* %a, <4 x i64> [[II]] 
; CHECK-NEXT:  [[A:%.*]] = call <4 x i32> @llvm.masked.gather.v4i32.v4p0i32(<4 x i32*> [[A_ADDR]], i32 4, <4 x i1> [[ACTIVE_INNER]], <4 x i32> undef)
; CHECK-NEXT:  [[FOUND_INNER:%.*]] = icmp eq <4 x i32> [[A]], [[NEEDLES]]
; CHECK-NEXT:  [[TRUNC_II:%.*]] = trunc <4 x i64> [[II]] to <4 x i32>
; CHECK-NEXT:  [[IDX_INNER_NEXT]] = select <4 x i1> [[FOUND_INNER]], <4 x i32> [[TRUNC_II]], <4 x i32> [[IDX_INNER]] 
; CHECK-NEXT:  [[IDX_OUT_INNER_NEXT]] = select <4 x i1> [[ACTIVE_INNER]], <4 x i32> [[IDX_INNER_NEXT]], <4 x i32> [[IDX_OUT_INNER]]
; CHECK-NEXT:  [[K_NEXT]] = add <4 x i64> [[K]], <i64 1, i64 1, i64 1, i64 1>
; CHECK-NEXT:  [[TMP7:%.*]] = insertelement <4 x i64> undef, i64 [[BIG_N2]], i64 0
; CHECK-NEXT:  [[TMP8:%.*]] = insertelement <4 x i64> [[TMP7]], i64 [[BIG_N2]], i64 1
; CHECK-NEXT:  [[TMP9:%.*]] = insertelement <4 x i64> [[TMP8]], i64 [[BIG_N2]], i64 2
; CHECK-NEXT:  [[BIG_N2_SPLAT:%.*]] = insertelement <4 x i64> [[TMP9]], i64 [[BIG_N2]], i64 3
; CHECK-NEXT:  [[K_GE_N:%.*]] = icmp sge <4 x i64> [[K_NEXT]], [[BIG_N2_SPLAT]]
; CHECK-NEXT:  [[INNER_DONE:%.*]] = or <4 x i1> [[FOUND_INNER]], [[K_GE_N]]
; CHECK-NEXT:  br label %[[LATCH_INNER]]

; CHECK:[[LATCH_INNER]]:
; CHECK-NEXT:  [[INNER_NOT_DONE:%.*]] = xor <4 x i1> [[INNER_DONE]], <i1 true, i1 true, i1 true, i1 true>
; CHECK-NEXT:  [[ACTIVE_INNER_NEXT]] = and <4 x i1> [[ACTIVE_INNER]], [[INNER_NOT_DONE]]
; CHECK-NEXT:  [[ANY_INNER_ACTIVE:%.*]] = call i1 @llvm.vector.reduce.or.v4i1(<4 x i1> [[ACTIVE_INNER_NEXT]])
; CHECK-NEXT:  br i1 [[ANY_INNER_ACTIVE]], label %[[HEADER_INNER]], label %[[EXIT_INNER:.*]]

; CHECK:[[EXIT_INNER]]:
; CHECK-NEXT:  br i1 [[N_GT_0]], label %[[IF_TRUE:.*]], label %[[IF_FALSE:.*]]

; CHECK:[[IF_TRUE]]:
; CHECK-NEXT:  br label %[[JOIN:.*]]

; CHECK:[[IF_FALSE]]:
; CHECK-NEXT:  br label %[[JOIN]]

; CHECK:[[JOIN]]:
; CHECK-NEXT:  [[IDX_NEXT:%.*]] = phi <4 x i32> [ [[IDX_OUT_INNER_NEXT]], %[[IF_TRUE]] ], [ <i32 -1, i32 -1, i32 -1, i32 -1>, %[[IF_FALSE]] ]
; CHECK-NEXT:  [[IDX_OUT_NEXT]] = select <4 x i1> [[ACTIVE_OUTER]], <4 x i32> [[IDX_NEXT]], <4 x i32> [[IDX_OUT]]
; CHECK-NEXT:  [[IDX_EQ_NEG]] = icmp eq <4 x i32> [[IDX_NEXT]], <i32 -1, i32 -1, i32 -1, i32 -1>
; CHECK-NEXT:  [[FOUND_OUT_NEXT]] = select <4 x i1> [[ACTIVE_OUTER]], <4 x i1> [[IDX_EQ_NEG]], <4 x i1> [[FOUND_OUT]]
; CHECK-NEXT:  [[J_NEXT]] = add <4 x i64> [[J]], <i64 1, i64 1, i64 1, i64 1>
; CHECK-NEXT:  [[J_DONE]] = icmp eq <4 x i64> [[J_NEXT]], [[N_SPLAT]]
; CHECK-NEXT:  br label %[[LATCH]]

; CHECK:[[DONE]]:
; CHECK-NEXT:  [[IDX_FINAL:%.*]] = phi <4 x i32> [ [[IDX_LOOP_OUT]], %exit ], [ <i32 -1, i32 -1, i32 -1, i32 -1>, %[[SKIP_LOOP]] ]
; CHECK-NEXT:  [[ADDR:%.*]] = bitcast i32* %indices to <4 x i32>*
; CHECK-NEXT:  store <4 x i32> [[IDX_FINAL]], <4 x i32>* [[ADDR]]

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @find(i32 %n, i32* noalias nocapture readonly %a, i32* noalias nocapture readonly %needles, i32* noalias nocapture %indices) local_unnamed_addr #0 {
entry:
  %cmp247 = icmp sgt i32 %n, 0
  %cmp643 = icmp sgt i32 %n, 0
  %0 = sext i32 %n to i64
  %1 = sext i32 %n to i64
  %2 = load i32, i32* %needles, align 4, !tbaa !3
  br i1 %cmp247, label %for.cond5.preheader.preheader, label %cleanup18

for.cond5.preheader.preheader:                    ; preds = %entry
  %wide.trip.count = zext i32 %n to i64
  br label %for.cond5.preheader

for.cond1:                                        ; preds = %cleanup12
  %exitcond.not = icmp eq i64 %indvars.iv.next54, %wide.trip.count
  br i1 %exitcond.not, label %cleanup18.loopexit, label %for.cond5.preheader, !llvm.loop !7

for.cond5.preheader:                              ; preds = %for.cond1, %for.cond5.preheader.preheader
  %indvars.iv53 = phi i64 [ 0, %for.cond5.preheader.preheader ], [ %indvars.iv.next54, %for.cond1 ]
  %3 = mul nsw i64 %indvars.iv53, %1
  br i1 %cmp643, label %for.body8.preheader, label %cleanup12

for.body8.preheader:                              ; preds = %for.cond5.preheader
  br label %for.body8

for.body8:                                        ; preds = %for.body8.preheader, %for.body8
  %indvars.iv = phi i64 [ %indvars.iv.next, %for.body8 ], [ 0, %for.body8.preheader ]
  %idx.144 = phi i32 [ %idx.2, %for.body8 ], [ -1, %for.body8.preheader ]
  %4 = add nsw i64 %indvars.iv, %3
  %arrayidx10 = getelementptr inbounds i32, i32* %a, i64 %4
  %5 = load i32, i32* %arrayidx10, align 4, !tbaa !3
  %cmp11 = icmp eq i32 %5, %2
  %6 = trunc i64 %4 to i32
  %idx.2 = select i1 %cmp11, i32 %6, i32 %idx.144
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %cmp6 = icmp sge i64 %indvars.iv.next, %0
  %7 = or i1 %cmp11, %cmp6
  br i1 %7, label %cleanup12.loopexit, label %for.body8, !llvm.loop !10

cleanup12.loopexit:                               ; preds = %for.body8
  %idx.2.lcssa = phi i32 [ %idx.2, %for.body8 ]
  br label %cleanup12

cleanup12:                                        ; preds = %cleanup12.loopexit, %for.cond5.preheader
  %idx.3 = phi i32 [ -1, %for.cond5.preheader ], [ %idx.2.lcssa, %cleanup12.loopexit ]
  %cmp13.not = icmp eq i32 %idx.3, -1
  %indvars.iv.next54 = add nuw nsw i64 %indvars.iv53, 1
  br i1 %cmp13.not, label %for.cond1, label %cleanup18.loopexit

cleanup18.loopexit:                               ; preds = %for.cond1, %cleanup12
  %idx.4.ph = phi i32 [ %idx.3, %cleanup12 ], [ -1, %for.cond1 ]
  br label %cleanup18

cleanup18:                                        ; preds = %cleanup18.loopexit, %entry
  %idx.4 = phi i32 [ -1, %entry ], [ %idx.4.ph, %cleanup18.loopexit ]
  store i32 %idx.4, i32* %indices, align 4, !tbaa !3
  %arrayidx.1 = getelementptr inbounds i32, i32* %needles, i64 1
  %8 = load i32, i32* %arrayidx.1, align 4, !tbaa !3
  br i1 %cmp247, label %for.cond5.preheader.preheader.1, label %cleanup18.1

for.cond5.preheader.preheader.1:                  ; preds = %cleanup18
  %wide.trip.count.1 = zext i32 %n to i64
  br label %for.cond5.preheader.1

for.cond5.preheader.1:                            ; preds = %for.cond1.1, %for.cond5.preheader.preheader.1
  %indvars.iv53.1 = phi i64 [ 0, %for.cond5.preheader.preheader.1 ], [ %indvars.iv.next54.1, %for.cond1.1 ]
  %9 = mul nsw i64 %indvars.iv53.1, %1
  br i1 %cmp643, label %for.body8.1.preheader, label %cleanup12.1

for.body8.1.preheader:                            ; preds = %for.cond5.preheader.1
  br label %for.body8.1

for.body8.1:                                      ; preds = %for.body8.1.preheader, %for.body8.1
  %indvars.iv.1 = phi i64 [ %indvars.iv.next.1, %for.body8.1 ], [ 0, %for.body8.1.preheader ]
  %idx.144.1 = phi i32 [ %idx.2.1, %for.body8.1 ], [ -1, %for.body8.1.preheader ]
  %10 = add nsw i64 %indvars.iv.1, %9
  %arrayidx10.1 = getelementptr inbounds i32, i32* %a, i64 %10
  %11 = load i32, i32* %arrayidx10.1, align 4, !tbaa !3
  %cmp11.1 = icmp eq i32 %11, %8
  %12 = trunc i64 %10 to i32
  %idx.2.1 = select i1 %cmp11.1, i32 %12, i32 %idx.144.1
  %indvars.iv.next.1 = add nuw nsw i64 %indvars.iv.1, 1
  %cmp6.1 = icmp sge i64 %indvars.iv.next.1, %0
  %13 = or i1 %cmp11.1, %cmp6.1
  br i1 %13, label %cleanup12.1.loopexit, label %for.body8.1, !llvm.loop !10

cleanup12.1.loopexit:                             ; preds = %for.body8.1
  %idx.2.1.lcssa = phi i32 [ %idx.2.1, %for.body8.1 ]
  br label %cleanup12.1

cleanup12.1:                                      ; preds = %cleanup12.1.loopexit, %for.cond5.preheader.1
  %idx.3.1 = phi i32 [ -1, %for.cond5.preheader.1 ], [ %idx.2.1.lcssa, %cleanup12.1.loopexit ]
  %cmp13.not.1 = icmp eq i32 %idx.3.1, -1
  %indvars.iv.next54.1 = add nuw nsw i64 %indvars.iv53.1, 1
  br i1 %cmp13.not.1, label %for.cond1.1, label %cleanup18.1.loopexit

for.cond1.1:                                      ; preds = %cleanup12.1
  %exitcond.1.not = icmp eq i64 %indvars.iv.next54.1, %wide.trip.count.1
  br i1 %exitcond.1.not, label %cleanup18.1.loopexit, label %for.cond5.preheader.1, !llvm.loop !7

cleanup18.1.loopexit:                             ; preds = %cleanup12.1, %for.cond1.1
  %idx.4.1.ph = phi i32 [ %idx.3.1, %cleanup12.1 ], [ -1, %for.cond1.1 ]
  br label %cleanup18.1

cleanup18.1:                                      ; preds = %cleanup18.1.loopexit, %cleanup18
  %idx.4.1 = phi i32 [ -1, %cleanup18 ], [ %idx.4.1.ph, %cleanup18.1.loopexit ]
  %arrayidx21.1 = getelementptr inbounds i32, i32* %indices, i64 1
  store i32 %idx.4.1, i32* %arrayidx21.1, align 4, !tbaa !3
  %arrayidx.2 = getelementptr inbounds i32, i32* %needles, i64 2
  %14 = load i32, i32* %arrayidx.2, align 4, !tbaa !3
  br i1 %cmp247, label %for.cond5.preheader.preheader.2, label %cleanup18.2

for.cond5.preheader.preheader.2:                  ; preds = %cleanup18.1
  %wide.trip.count.2 = zext i32 %n to i64
  br label %for.cond5.preheader.2

for.cond5.preheader.2:                            ; preds = %for.cond1.2, %for.cond5.preheader.preheader.2
  %indvars.iv53.2 = phi i64 [ 0, %for.cond5.preheader.preheader.2 ], [ %indvars.iv.next54.2, %for.cond1.2 ]
  %15 = mul nsw i64 %indvars.iv53.2, %1
  br i1 %cmp643, label %for.body8.2.preheader, label %cleanup12.2

for.body8.2.preheader:                            ; preds = %for.cond5.preheader.2
  br label %for.body8.2

for.body8.2:                                      ; preds = %for.body8.2.preheader, %for.body8.2
  %indvars.iv.2 = phi i64 [ %indvars.iv.next.2, %for.body8.2 ], [ 0, %for.body8.2.preheader ]
  %idx.144.2 = phi i32 [ %idx.2.2, %for.body8.2 ], [ -1, %for.body8.2.preheader ]
  %16 = add nsw i64 %indvars.iv.2, %15
  %arrayidx10.2 = getelementptr inbounds i32, i32* %a, i64 %16
  %17 = load i32, i32* %arrayidx10.2, align 4, !tbaa !3
  %cmp11.2 = icmp eq i32 %17, %14
  %18 = trunc i64 %16 to i32
  %idx.2.2 = select i1 %cmp11.2, i32 %18, i32 %idx.144.2
  %indvars.iv.next.2 = add nuw nsw i64 %indvars.iv.2, 1
  %cmp6.2 = icmp sge i64 %indvars.iv.next.2, %0
  %19 = or i1 %cmp11.2, %cmp6.2
  br i1 %19, label %cleanup12.2.loopexit, label %for.body8.2, !llvm.loop !10

cleanup12.2.loopexit:                             ; preds = %for.body8.2
  %idx.2.2.lcssa = phi i32 [ %idx.2.2, %for.body8.2 ]
  br label %cleanup12.2

cleanup12.2:                                      ; preds = %cleanup12.2.loopexit, %for.cond5.preheader.2
  %idx.3.2 = phi i32 [ -1, %for.cond5.preheader.2 ], [ %idx.2.2.lcssa, %cleanup12.2.loopexit ]
  %cmp13.not.2 = icmp eq i32 %idx.3.2, -1
  %indvars.iv.next54.2 = add nuw nsw i64 %indvars.iv53.2, 1
  br i1 %cmp13.not.2, label %for.cond1.2, label %cleanup18.2.loopexit

for.cond1.2:                                      ; preds = %cleanup12.2
  %exitcond.2.not = icmp eq i64 %indvars.iv.next54.2, %wide.trip.count.2
  br i1 %exitcond.2.not, label %cleanup18.2.loopexit, label %for.cond5.preheader.2, !llvm.loop !7

cleanup18.2.loopexit:                             ; preds = %cleanup12.2, %for.cond1.2
  %idx.4.2.ph = phi i32 [ %idx.3.2, %cleanup12.2 ], [ -1, %for.cond1.2 ]
  br label %cleanup18.2

cleanup18.2:                                      ; preds = %cleanup18.2.loopexit, %cleanup18.1
  %idx.4.2 = phi i32 [ -1, %cleanup18.1 ], [ %idx.4.2.ph, %cleanup18.2.loopexit ]
  %arrayidx21.2 = getelementptr inbounds i32, i32* %indices, i64 2
  store i32 %idx.4.2, i32* %arrayidx21.2, align 4, !tbaa !3
  %arrayidx.3 = getelementptr inbounds i32, i32* %needles, i64 3
  %20 = load i32, i32* %arrayidx.3, align 4, !tbaa !3
  br i1 %cmp247, label %for.cond5.preheader.preheader.3, label %cleanup18.3

for.cond5.preheader.preheader.3:                  ; preds = %cleanup18.2
  %wide.trip.count.3 = zext i32 %n to i64
  br label %for.cond5.preheader.3

for.cond5.preheader.3:                            ; preds = %for.cond1.3, %for.cond5.preheader.preheader.3
  %indvars.iv53.3 = phi i64 [ 0, %for.cond5.preheader.preheader.3 ], [ %indvars.iv.next54.3, %for.cond1.3 ]
  %21 = mul nsw i64 %indvars.iv53.3, %1
  br i1 %cmp643, label %for.body8.3.preheader, label %cleanup12.3

for.body8.3.preheader:                            ; preds = %for.cond5.preheader.3
  br label %for.body8.3

for.body8.3:                                      ; preds = %for.body8.3.preheader, %for.body8.3
  %indvars.iv.3 = phi i64 [ %indvars.iv.next.3, %for.body8.3 ], [ 0, %for.body8.3.preheader ]
  %idx.144.3 = phi i32 [ %idx.2.3, %for.body8.3 ], [ -1, %for.body8.3.preheader ]
  %22 = add nsw i64 %indvars.iv.3, %21
  %arrayidx10.3 = getelementptr inbounds i32, i32* %a, i64 %22
  %23 = load i32, i32* %arrayidx10.3, align 4, !tbaa !3
  %cmp11.3 = icmp eq i32 %23, %20
  %24 = trunc i64 %22 to i32
  %idx.2.3 = select i1 %cmp11.3, i32 %24, i32 %idx.144.3
  %indvars.iv.next.3 = add nuw nsw i64 %indvars.iv.3, 1
  %cmp6.3 = icmp sge i64 %indvars.iv.next.3, %0
  %25 = or i1 %cmp11.3, %cmp6.3
  br i1 %25, label %cleanup12.3.loopexit, label %for.body8.3, !llvm.loop !10

cleanup12.3.loopexit:                             ; preds = %for.body8.3
  %idx.2.3.lcssa = phi i32 [ %idx.2.3, %for.body8.3 ]
  br label %cleanup12.3

cleanup12.3:                                      ; preds = %cleanup12.3.loopexit, %for.cond5.preheader.3
  %idx.3.3 = phi i32 [ -1, %for.cond5.preheader.3 ], [ %idx.2.3.lcssa, %cleanup12.3.loopexit ]
  %cmp13.not.3 = icmp eq i32 %idx.3.3, -1
  %indvars.iv.next54.3 = add nuw nsw i64 %indvars.iv53.3, 1
  br i1 %cmp13.not.3, label %for.cond1.3, label %cleanup18.3.loopexit

for.cond1.3:                                      ; preds = %cleanup12.3
  %exitcond.3.not = icmp eq i64 %indvars.iv.next54.3, %wide.trip.count.3
  br i1 %exitcond.3.not, label %cleanup18.3.loopexit, label %for.cond5.preheader.3, !llvm.loop !7

cleanup18.3.loopexit:                             ; preds = %cleanup12.3, %for.cond1.3
  %idx.4.3.ph = phi i32 [ %idx.3.3, %cleanup12.3 ], [ -1, %for.cond1.3 ]
  br label %cleanup18.3

cleanup18.3:                                      ; preds = %cleanup18.3.loopexit, %cleanup18.2
  %idx.4.3 = phi i32 [ -1, %cleanup18.2 ], [ %idx.4.3.ph, %cleanup18.3.loopexit ]
  %arrayidx21.3 = getelementptr inbounds i32, i32* %indices, i64 3
  store i32 %idx.4.3, i32* %arrayidx21.3, align 4, !tbaa !3
  ret void
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="icelake-client" "target-features"="+64bit,+adx,+aes,+avx,+avx2,+avx512bitalg,+avx512bw,+avx512cd,+avx512dq,+avx512f,+avx512ifma,+avx512vbmi,+avx512vbmi2,+avx512vl,+avx512vnni,+avx512vpopcntdq,+bmi,+bmi2,+clflushopt,+cmov,+cx16,+cx8,+f16c,+fma,+fsgsbase,+fxsr,+gfni,+invpcid,+lzcnt,+mmx,+movbe,+pclmul,+popcnt,+prfchw,+rdpid,+rdrnd,+rdseed,+sahf,+sgx,+sha,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+ssse3,+vaes,+vpclmulqdq,+x87,+xsave,+xsavec,+xsaveopt,+xsaves,-amx-bf16,-amx-int8,-amx-tile,-avx512bf16,-avx512er,-avx512pf,-avx512vp2intersect,-avxvnni,-cldemote,-clwb,-clzero,-enqcmd,-fma4,-hreset,-kl,-lwp,-movdir64b,-movdiri,-mwaitx,-pconfig,-pku,-prefetchwt1,-ptwrite,-rtm,-serialize,-shstk,-sse4a,-tbm,-tsxldtrk,-uintr,-waitpkg,-wbnoinvd,-widekl,-xop" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = distinct !{!7, !8, !9}
!8 = !{!"llvm.loop.mustprogress"}
!9 = !{!"llvm.loop.unroll.disable"}
!10 = distinct !{!10, !8, !9}
