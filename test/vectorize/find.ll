; RUN: %opt -gslp -adce -no-unroll %s -S | FileCheck %s

; CHECK:  %cmp224 = icmp sgt i32 %n, 0
; CHECK-NEXT:  [[NEEDLES_ADDR:%.*]] = bitcast i32* %needles to <4 x i32>*
; CHECK-NEXT:  [[NEEDLES:%.*]] = load <4 x i32>, <4 x i32>* [[NEEDLES_ADDR]], align 4, !tbaa !3
; CHECK-NEXT:  br i1 %cmp224, label %[[PREHEADER:.*]], label %[[SKIP_LOOP:.*]]

; CHECK: [[PREHEADER]]:
; CHECK-NOT: br
; CHECK:  [[N_SPLAT:%.*]] = zext <4 x i32> %4 to <4 x i64>
; CHECK-NEXT:  br label %[[HEADER:.*]]

; CHECK: [[SKIP_LOOP]]:
; CHECK-NEXT:  br label %[[DONE:.*]]

; CHECK: [[HEADER]]:
; CHECK-DAG:  [[FOUND_OUT:%.*]] = phi <4 x i1> [ undef, %2 ], [ [[NEXT_FOUND_OUT:%.*]], %[[LATCH:.*]] ]
; CHECK-DAG:  [[IDX_OUT:%.*]] = phi <4 x i64> [ undef, %[[PREHEADER]] ], [ [[NEXT_IDX_OUT:%.*]], %[[LATCH]] ]
; CHECK-DAG:  [[IDX:%.*]] = phi <4 x i64> [ zeroinitializer, %[[PREHEADER]] ], [ [[IDX_NEXT:%.*]], %[[LATCH]] ]
; CHECK-DAG:  [[ACTIVE:%.*]] = phi <4 x i1> [ <i1 true, i1 true, i1 true, i1 true>, %2 ], [ [[ACTIVE_NEXT:%.*]], %[[LATCH]] ]
; CHECK-NEXT:  [[NEXT_IDX_OUT]] = select <4 x i1> [[ACTIVE]], <4 x i64> [[IDX]], <4 x i64> [[IDX_OUT]]
; CHECK-NEXT:  [[ADDRS:%.*]] = getelementptr i32, i32* %a, <4 x i64> [[IDX]]
; CHECK-NEXT:  [[GATHER:%.*]] = call <4 x i32> @llvm.masked.gather.v4i32.v4p0i32(<4 x i32*> [[ADDRS]], i32 4, <4 x i1> [[ACTIVE]], <4 x i32> undef)
; CHECK-NEXT:  [[FOUND:%.*]] = icmp eq <4 x i32> [[GATHER]], [[NEEDLES]]
; CHECK-NEXT:  [[NEXT_FOUND_OUT]] = select <4 x i1> [[ACTIVE]], <4 x i1> [[FOUND]], <4 x i1> [[FOUND_OUT]]
; CHECK-NEXT:  [[IDX_NEXT]] = add <4 x i64> [[IDX]], <i64 1, i64 1, i64 1, i64 1>
; CHECK-NEXT:  [[LT_N:%.*]] = icmp eq <4 x i64> [[IDX_NEXT]], [[N_SPLAT]]
; CHECK-NEXT:  br label %[[LATCH]]

; CHECK: [[LATCH]]:
; CHECK-NEXT:  [[NOT_LT_N:%.*]] = xor <4 x i1> [[LT_N]], <i1 true, i1 true, i1 true, i1 true>
; CHECK-NEXT:  [[NOT_FOUND:%.*]] = xor <4 x i1> [[FOUND]], <i1 true, i1 true, i1 true, i1 true>
; CHECK-NEXT:  [[TMP:%.*]] = and <4 x i1> [[NOT_FOUND]], [[NOT_LT_N]]
; CHECK-NEXT:  [[ACTIVE_NEXT]] = and <4 x i1> [[ACTIVE]], [[TMP]]
; CHECK-NEXT:  [[SOME_ACTIVE:%.*]] = call i1 @llvm.vector.reduce.or.v4i1(<4 x i1> [[ACTIVE_NEXT]])
; CHECK-NEXT:  br i1 [[SOME_ACTIVE]], label %[[HEADER]], label %[[EXIT:.*]]

; CHECK: [[EXIT]]:
; CHECK-NEXT:  [[MATCHED_IDXS:%.*]] = select <4 x i1> [[NEXT_FOUND_OUT]], <4 x i64> [[NEXT_IDX_OUT]], <4 x i64> <i64 -1, i64 -1, i64 -1, i64 -1>
; CHECK-NEXT:  br label %[[DONE]]

; CHECK: [[DONE]]:
; CHECK-NEXT:  [[PHI:%.*]] = phi <4 x i64> [ [[MATCHED_IDXS]], %[[EXIT]] ], [ <i64 -1, i64 -1, i64 -1, i64 -1>, %[[SKIP_LOOP]] ]
; CHECK-NEXT:  [[SHL:%.*]] = shl <4 x i64> [[PHI]], <i64 32, i64 32, i64 32, i64 32>
; CHECK-NEXT:  [[ASHR:%.*]] = ashr <4 x i64> [[SHL]], <i64 32, i64 32, i64 32, i64 32>
; CHECK-NEXT:  [[OUT_ADDR:%.*]] = bitcast i64* %indices to <4 x i64>*
; CHECK-NEXT:  store <4 x i64> [[ASHR]], <4 x i64>* [[OUT_ADDR]], align 8, !tbaa !7
; CHECK-NEXT:  ret void

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @find(i32 %n, i32* noalias nocapture readonly %a, i32* noalias nocapture readonly %needles, i64* noalias nocapture %indices) local_unnamed_addr #0 {
entry:
  %cmp224 = icmp sgt i32 %n, 0
  %0 = load i32, i32* %needles, align 4, !tbaa !3
  br i1 %cmp224, label %for.body4.preheader, label %cleanup

for.body4.preheader:                              ; preds = %entry
  %wide.trip.count = zext i32 %n to i64
  br label %for.body4

for.body4:                                        ; preds = %for.inc, %for.body4.preheader
  %indvars.iv = phi i64 [ 0, %for.body4.preheader ], [ %indvars.iv.next, %for.inc ]
  %arrayidx6 = getelementptr inbounds i32, i32* %a, i64 %indvars.iv
  %1 = load i32, i32* %arrayidx6, align 4, !tbaa !3
  %cmp7 = icmp eq i32 %1, %0
  br i1 %cmp7, label %cleanup.loopexit, label %for.inc

for.inc:                                          ; preds = %for.body4
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %cleanup.loopexit, label %for.body4, !llvm.loop !7

cleanup.loopexit:                                 ; preds = %for.body4, %for.inc
  %idx.0.ph = phi i64 [ %indvars.iv, %for.body4 ], [ -1, %for.inc ]
  br label %cleanup

cleanup:                                          ; preds = %cleanup.loopexit, %entry
  %idx.0 = phi i64 [ -1, %entry ], [ %idx.0.ph, %cleanup.loopexit ]
  %sext = shl i64 %idx.0, 32
  %conv = ashr exact i64 %sext, 32
  store i64 %conv, i64* %indices, align 8, !tbaa !10
  %arrayidx.1 = getelementptr inbounds i32, i32* %needles, i64 1
  %2 = load i32, i32* %arrayidx.1, align 4, !tbaa !3
  br i1 %cmp224, label %for.body4.preheader.1, label %cleanup.1

for.body4.preheader.1:                            ; preds = %cleanup
  %wide.trip.count.1 = zext i32 %n to i64
  br label %for.body4.1

for.body4.1:                                      ; preds = %for.inc.1, %for.body4.preheader.1
  %indvars.iv.1 = phi i64 [ 0, %for.body4.preheader.1 ], [ %indvars.iv.next.1, %for.inc.1 ]
  %arrayidx6.1 = getelementptr inbounds i32, i32* %a, i64 %indvars.iv.1
  %3 = load i32, i32* %arrayidx6.1, align 4, !tbaa !3
  %cmp7.1 = icmp eq i32 %3, %2
  br i1 %cmp7.1, label %cleanup.1.loopexit, label %for.inc.1

for.inc.1:                                        ; preds = %for.body4.1
  %indvars.iv.next.1 = add nuw nsw i64 %indvars.iv.1, 1
  %exitcond.1.not = icmp eq i64 %indvars.iv.next.1, %wide.trip.count.1
  br i1 %exitcond.1.not, label %cleanup.1.loopexit, label %for.body4.1, !llvm.loop !7

cleanup.1.loopexit:                               ; preds = %for.body4.1, %for.inc.1
  %idx.0.1.ph = phi i64 [ %indvars.iv.1, %for.body4.1 ], [ -1, %for.inc.1 ]
  br label %cleanup.1

cleanup.1:                                        ; preds = %cleanup.1.loopexit, %cleanup
  %idx.0.1 = phi i64 [ -1, %cleanup ], [ %idx.0.1.ph, %cleanup.1.loopexit ]
  %sext31 = shl i64 %idx.0.1, 32
  %conv.1 = ashr exact i64 %sext31, 32
  %arrayidx9.1 = getelementptr inbounds i64, i64* %indices, i64 1
  store i64 %conv.1, i64* %arrayidx9.1, align 8, !tbaa !10
  %arrayidx.2 = getelementptr inbounds i32, i32* %needles, i64 2
  %4 = load i32, i32* %arrayidx.2, align 4, !tbaa !3
  br i1 %cmp224, label %for.body4.preheader.2, label %cleanup.2

for.body4.preheader.2:                            ; preds = %cleanup.1
  %wide.trip.count.2 = zext i32 %n to i64
  br label %for.body4.2

for.body4.2:                                      ; preds = %for.inc.2, %for.body4.preheader.2
  %indvars.iv.2 = phi i64 [ 0, %for.body4.preheader.2 ], [ %indvars.iv.next.2, %for.inc.2 ]
  %arrayidx6.2 = getelementptr inbounds i32, i32* %a, i64 %indvars.iv.2
  %5 = load i32, i32* %arrayidx6.2, align 4, !tbaa !3
  %cmp7.2 = icmp eq i32 %5, %4
  br i1 %cmp7.2, label %cleanup.2.loopexit, label %for.inc.2

for.inc.2:                                        ; preds = %for.body4.2
  %indvars.iv.next.2 = add nuw nsw i64 %indvars.iv.2, 1
  %exitcond.2.not = icmp eq i64 %indvars.iv.next.2, %wide.trip.count.2
  br i1 %exitcond.2.not, label %cleanup.2.loopexit, label %for.body4.2, !llvm.loop !7

cleanup.2.loopexit:                               ; preds = %for.body4.2, %for.inc.2
  %idx.0.2.ph = phi i64 [ %indvars.iv.2, %for.body4.2 ], [ -1, %for.inc.2 ]
  br label %cleanup.2

cleanup.2:                                        ; preds = %cleanup.2.loopexit, %cleanup.1
  %idx.0.2 = phi i64 [ -1, %cleanup.1 ], [ %idx.0.2.ph, %cleanup.2.loopexit ]
  %sext32 = shl i64 %idx.0.2, 32
  %conv.2 = ashr exact i64 %sext32, 32
  %arrayidx9.2 = getelementptr inbounds i64, i64* %indices, i64 2
  store i64 %conv.2, i64* %arrayidx9.2, align 8, !tbaa !10
  %arrayidx.3 = getelementptr inbounds i32, i32* %needles, i64 3
  %6 = load i32, i32* %arrayidx.3, align 4, !tbaa !3
  br i1 %cmp224, label %for.body4.preheader.3, label %cleanup.3

for.body4.preheader.3:                            ; preds = %cleanup.2
  %wide.trip.count.3 = zext i32 %n to i64
  br label %for.body4.3

for.body4.3:                                      ; preds = %for.inc.3, %for.body4.preheader.3
  %indvars.iv.3 = phi i64 [ 0, %for.body4.preheader.3 ], [ %indvars.iv.next.3, %for.inc.3 ]
  %arrayidx6.3 = getelementptr inbounds i32, i32* %a, i64 %indvars.iv.3
  %7 = load i32, i32* %arrayidx6.3, align 4, !tbaa !3
  %cmp7.3 = icmp eq i32 %7, %6
  br i1 %cmp7.3, label %cleanup.3.loopexit, label %for.inc.3

for.inc.3:                                        ; preds = %for.body4.3
  %indvars.iv.next.3 = add nuw nsw i64 %indvars.iv.3, 1
  %exitcond.3.not = icmp eq i64 %indvars.iv.next.3, %wide.trip.count.3
  br i1 %exitcond.3.not, label %cleanup.3.loopexit, label %for.body4.3, !llvm.loop !7

cleanup.3.loopexit:                               ; preds = %for.body4.3, %for.inc.3
  %idx.0.3.ph = phi i64 [ %indvars.iv.3, %for.body4.3 ], [ -1, %for.inc.3 ]
  br label %cleanup.3

cleanup.3:                                        ; preds = %cleanup.3.loopexit, %cleanup.2
  %idx.0.3 = phi i64 [ -1, %cleanup.2 ], [ %idx.0.3.ph, %cleanup.3.loopexit ]
  %sext33 = shl i64 %idx.0.3, 32
  %conv.3 = ashr exact i64 %sext33, 32
  %arrayidx9.3 = getelementptr inbounds i64, i64* %indices, i64 3
  store i64 %conv.3, i64* %arrayidx9.3, align 8, !tbaa !10
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
!10 = !{!11, !11, i64 0}
!11 = !{!"long long", !5, i64 0}
