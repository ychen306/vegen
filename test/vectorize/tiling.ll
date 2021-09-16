; RUN: %opt %s -gslp -no-unroll -o - -S | FileCheck %s
; RUN: %opt %s -gslp -no-unroll -verify -o %t -S && %check-function  3 'int matvec(int, int, int, int*, int*, int*)' 'matvec(30, 15, 3, %%s, %%s, %%s)' %t %s

target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; For now, just make sure some thing is vectorized
; CHECK: <{{.*}}x{{.*}}>

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @matvec(i32 %n, i32 %m, i32 %l, i32* noalias nocapture readonly %A, i32* noalias nocapture readonly %B, i32* noalias nocapture %C) local_unnamed_addr #0 {
entry:
  %0 = zext i32 %l to i64
  %1 = zext i32 %m to i64
  %cmp48 = icmp sgt i32 %n, 0
  br i1 %cmp48, label %for.cond1.preheader.lr.ph, label %for.cond.cleanup

for.cond1.preheader.lr.ph:                        ; preds = %entry
  %cmp245 = icmp sgt i32 %m, 0
  %cmp643 = icmp sgt i32 %l, 0
  %2 = add i32 %m, -1
  %xtraiter60 = and i32 %n, 1
  %3 = icmp eq i32 %n, 1
  br i1 %3, label %for.cond.cleanup.loopexit.unr-lcssa, label %for.cond1.preheader.lr.ph.new

for.cond1.preheader.lr.ph.new:                    ; preds = %for.cond1.preheader.lr.ph
  %unroll_iter82 = and i32 %n, -2
  br label %for.cond1.preheader

for.cond1.preheader:                              ; preds = %for.cond.cleanup3.1, %for.cond1.preheader.lr.ph.new
  %indvars.iv56 = phi i64 [ 0, %for.cond1.preheader.lr.ph.new ], [ %indvars.iv.next57.1, %for.cond.cleanup3.1 ]
  %niter83 = phi i32 [ %unroll_iter82, %for.cond1.preheader.lr.ph.new ], [ %niter83.nsub.1, %for.cond.cleanup3.1 ]
  br i1 %cmp245, label %for.cond5.preheader.lr.ph, label %for.cond.cleanup3

for.cond5.preheader.lr.ph:                        ; preds = %for.cond1.preheader
  %4 = mul nuw nsw i64 %indvars.iv56, %0
  %arrayidx = getelementptr inbounds i32, i32* %A, i64 %4
  %5 = mul nuw nsw i64 %indvars.iv56, %1
  %arrayidx16 = getelementptr inbounds i32, i32* %C, i64 %5
  %xtraiter = and i32 %m, 1
  %6 = icmp eq i32 %2, 0
  br i1 %6, label %for.cond.cleanup3.loopexit.unr-lcssa, label %for.cond5.preheader.lr.ph.new

for.cond5.preheader.lr.ph.new:                    ; preds = %for.cond5.preheader.lr.ph
  %unroll_iter = and i32 %m, -2
  br label %for.cond5.preheader

for.cond.cleanup.loopexit.unr-lcssa:              ; preds = %for.cond.cleanup3.1, %for.cond1.preheader.lr.ph
  %indvars.iv56.unr = phi i64 [ 0, %for.cond1.preheader.lr.ph ], [ %indvars.iv.next57.1, %for.cond.cleanup3.1 ]
  %lcmp.mod81.not = icmp ne i32 %xtraiter60, 0
  %7 = and i1 %cmp245, %lcmp.mod81.not
  br i1 %7, label %for.cond5.preheader.lr.ph.epil, label %for.cond.cleanup

for.cond5.preheader.lr.ph.epil:                   ; preds = %for.cond.cleanup.loopexit.unr-lcssa
  %8 = mul nuw nsw i64 %indvars.iv56.unr, %0
  %arrayidx.epil = getelementptr inbounds i32, i32* %A, i64 %8
  %9 = mul nuw nsw i64 %indvars.iv56.unr, %1
  %arrayidx16.epil = getelementptr inbounds i32, i32* %C, i64 %9
  %xtraiter.epil = and i32 %m, 1
  %10 = icmp eq i32 %2, 0
  br i1 %10, label %for.cond.cleanup3.loopexit.unr-lcssa.epil, label %for.cond5.preheader.lr.ph.new.epil

for.cond5.preheader.lr.ph.new.epil:               ; preds = %for.cond5.preheader.lr.ph.epil
  %unroll_iter.epil = and i32 %m, -2
  br label %for.cond5.preheader.epil61

for.cond5.preheader.epil61:                       ; preds = %for.cond.cleanup7.1.epil, %for.cond5.preheader.lr.ph.new.epil
  %indvars.iv52.epil62 = phi i64 [ 0, %for.cond5.preheader.lr.ph.new.epil ], [ %indvars.iv.next53.1.epil, %for.cond.cleanup7.1.epil ]
  %niter.epil = phi i32 [ %unroll_iter.epil, %for.cond5.preheader.lr.ph.new.epil ], [ %niter.nsub.1.epil, %for.cond.cleanup7.1.epil ]
  br i1 %cmp643, label %for.body8.lr.ph.epil63, label %for.cond.cleanup7.epil79

for.body8.lr.ph.epil63:                           ; preds = %for.cond5.preheader.epil61
  %arrayidx18.epil64 = getelementptr inbounds i32, i32* %arrayidx16.epil, i64 %indvars.iv52.epil62
  %arrayidx18.promoted.epil65 = load i32, i32* %arrayidx18.epil64, align 4, !tbaa !3
  %wide.trip.count.epil66 = zext i32 %l to i64
  br label %for.body8.epil67

for.body8.epil67:                                 ; preds = %for.body8.epil67, %for.body8.lr.ph.epil63
  %indvars.iv.epil68 = phi i64 [ 0, %for.body8.lr.ph.epil63 ], [ %indvars.iv.next.epil75, %for.body8.epil67 ]
  %add51.epil69 = phi i32 [ %arrayidx18.promoted.epil65, %for.body8.lr.ph.epil63 ], [ %add.epil74, %for.body8.epil67 ]
  %arrayidx10.epil70 = getelementptr inbounds i32, i32* %arrayidx.epil, i64 %indvars.iv.epil68
  %11 = load i32, i32* %arrayidx10.epil70, align 4, !tbaa !3
  %12 = mul nuw nsw i64 %indvars.iv.epil68, %1
  %arrayidx12.epil71 = getelementptr inbounds i32, i32* %B, i64 %indvars.iv52.epil62
  %arrayidx14.epil72 = getelementptr inbounds i32, i32* %arrayidx12.epil71, i64 %12
  %13 = load i32, i32* %arrayidx14.epil72, align 4, !tbaa !3
  %mul.epil73 = mul nsw i32 %13, %11
  %add.epil74 = add nsw i32 %add51.epil69, %mul.epil73
  %indvars.iv.next.epil75 = add nuw nsw i64 %indvars.iv.epil68, 1
  %exitcond.epil76.not = icmp eq i64 %indvars.iv.next.epil75, %wide.trip.count.epil66
  br i1 %exitcond.epil76.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil77, label %for.body8.epil67, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.epil77:     ; preds = %for.body8.epil67
  store i32 %add.epil74, i32* %arrayidx18.epil64, align 4, !tbaa !3
  br label %for.cond.cleanup7.epil79

for.cond.cleanup7.epil79:                         ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil77, %for.cond5.preheader.epil61
  %indvars.iv.next53.epil80 = or i64 %indvars.iv52.epil62, 1
  br i1 %cmp643, label %for.body8.lr.ph.1.epil, label %for.cond.cleanup7.1.epil

for.body8.lr.ph.1.epil:                           ; preds = %for.cond.cleanup7.epil79
  %arrayidx18.1.epil = getelementptr inbounds i32, i32* %arrayidx16.epil, i64 %indvars.iv.next53.epil80
  %arrayidx18.promoted.1.epil = load i32, i32* %arrayidx18.1.epil, align 4, !tbaa !3
  %wide.trip.count.1.epil = zext i32 %l to i64
  br label %for.body8.1.epil

for.body8.1.epil:                                 ; preds = %for.body8.1.epil, %for.body8.lr.ph.1.epil
  %indvars.iv.1.epil = phi i64 [ 0, %for.body8.lr.ph.1.epil ], [ %indvars.iv.next.1.epil, %for.body8.1.epil ]
  %add51.1.epil = phi i32 [ %arrayidx18.promoted.1.epil, %for.body8.lr.ph.1.epil ], [ %add.1.epil, %for.body8.1.epil ]
  %arrayidx10.1.epil = getelementptr inbounds i32, i32* %arrayidx.epil, i64 %indvars.iv.1.epil
  %14 = load i32, i32* %arrayidx10.1.epil, align 4, !tbaa !3
  %15 = mul nuw nsw i64 %indvars.iv.1.epil, %1
  %arrayidx12.1.epil = getelementptr inbounds i32, i32* %B, i64 %indvars.iv.next53.epil80
  %arrayidx14.1.epil = getelementptr inbounds i32, i32* %arrayidx12.1.epil, i64 %15
  %16 = load i32, i32* %arrayidx14.1.epil, align 4, !tbaa !3
  %mul.1.epil = mul nsw i32 %16, %14
  %add.1.epil = add nsw i32 %add51.1.epil, %mul.1.epil
  %indvars.iv.next.1.epil = add nuw nsw i64 %indvars.iv.1.epil, 1
  %exitcond.1.epil.not = icmp eq i64 %indvars.iv.next.1.epil, %wide.trip.count.1.epil
  br i1 %exitcond.1.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.epil, label %for.body8.1.epil, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.1.epil:     ; preds = %for.body8.1.epil
  store i32 %add.1.epil, i32* %arrayidx18.1.epil, align 4, !tbaa !3
  br label %for.cond.cleanup7.1.epil

for.cond.cleanup7.1.epil:                         ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.epil, %for.cond.cleanup7.epil79
  %indvars.iv.next53.1.epil = add nuw nsw i64 %indvars.iv52.epil62, 2
  %niter.nsub.1.epil = add i32 %niter.epil, -2
  %niter.ncmp.1.epil.not = icmp eq i32 %niter.nsub.1.epil, 0
  br i1 %niter.ncmp.1.epil.not, label %for.cond.cleanup3.loopexit.unr-lcssa.epil, label %for.cond5.preheader.epil61, !llvm.loop !10

for.cond.cleanup3.loopexit.unr-lcssa.epil:        ; preds = %for.cond.cleanup7.1.epil, %for.cond5.preheader.lr.ph.epil
  %indvars.iv52.unr.epil = phi i64 [ 0, %for.cond5.preheader.lr.ph.epil ], [ %indvars.iv.next53.1.epil, %for.cond.cleanup7.1.epil ]
  %lcmp.mod.epil.not = icmp ne i32 %xtraiter.epil, 0
  %17 = and i1 %cmp643, %lcmp.mod.epil.not
  br i1 %17, label %for.body8.lr.ph.epil.epil, label %for.cond.cleanup

for.body8.lr.ph.epil.epil:                        ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.epil
  %arrayidx18.epil.epil = getelementptr inbounds i32, i32* %arrayidx16.epil, i64 %indvars.iv52.unr.epil
  %arrayidx18.promoted.epil.epil = load i32, i32* %arrayidx18.epil.epil, align 4, !tbaa !3
  %wide.trip.count.epil.epil = zext i32 %l to i64
  br label %for.body8.epil.epil

for.body8.epil.epil:                              ; preds = %for.body8.epil.epil, %for.body8.lr.ph.epil.epil
  %indvars.iv.epil.epil = phi i64 [ 0, %for.body8.lr.ph.epil.epil ], [ %indvars.iv.next.epil.epil, %for.body8.epil.epil ]
  %add51.epil.epil = phi i32 [ %arrayidx18.promoted.epil.epil, %for.body8.lr.ph.epil.epil ], [ %add.epil.epil, %for.body8.epil.epil ]
  %arrayidx10.epil.epil = getelementptr inbounds i32, i32* %arrayidx.epil, i64 %indvars.iv.epil.epil
  %18 = load i32, i32* %arrayidx10.epil.epil, align 4, !tbaa !3
  %19 = mul nuw nsw i64 %indvars.iv.epil.epil, %1
  %arrayidx12.epil.epil = getelementptr inbounds i32, i32* %B, i64 %indvars.iv52.unr.epil
  %arrayidx14.epil.epil = getelementptr inbounds i32, i32* %arrayidx12.epil.epil, i64 %19
  %20 = load i32, i32* %arrayidx14.epil.epil, align 4, !tbaa !3
  %mul.epil.epil = mul nsw i32 %20, %18
  %add.epil.epil = add nsw i32 %add51.epil.epil, %mul.epil.epil
  %indvars.iv.next.epil.epil = add nuw nsw i64 %indvars.iv.epil.epil, 1
  %exitcond.epil.epil.not = icmp eq i64 %indvars.iv.next.epil.epil, %wide.trip.count.epil.epil
  br i1 %exitcond.epil.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.epil, label %for.body8.epil.epil, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.epil.epil:  ; preds = %for.body8.epil.epil
  store i32 %add.epil.epil, i32* %arrayidx18.epil.epil, align 4, !tbaa !3
  br label %for.cond.cleanup

for.cond.cleanup:                                 ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.epil, %for.cond.cleanup.loopexit.unr-lcssa, %for.cond5.for.cond.cleanup7_crit_edge.epil.epil, %entry
  ret void

for.cond5.preheader:                              ; preds = %for.cond.cleanup7.1, %for.cond5.preheader.lr.ph.new
  %indvars.iv52 = phi i64 [ 0, %for.cond5.preheader.lr.ph.new ], [ %indvars.iv.next53.1, %for.cond.cleanup7.1 ]
  %niter = phi i32 [ %unroll_iter, %for.cond5.preheader.lr.ph.new ], [ %niter.nsub.1, %for.cond.cleanup7.1 ]
  br i1 %cmp643, label %for.body8.lr.ph, label %for.cond.cleanup7

for.body8.lr.ph:                                  ; preds = %for.cond5.preheader
  %arrayidx18 = getelementptr inbounds i32, i32* %arrayidx16, i64 %indvars.iv52
  %arrayidx18.promoted = load i32, i32* %arrayidx18, align 4, !tbaa !3
  %wide.trip.count = zext i32 %l to i64
  br label %body1

for.cond.cleanup3.loopexit.unr-lcssa:             ; preds = %for.cond.cleanup7.1, %for.cond5.preheader.lr.ph
  %indvars.iv52.unr = phi i64 [ 0, %for.cond5.preheader.lr.ph ], [ %indvars.iv.next53.1, %for.cond.cleanup7.1 ]
  %lcmp.mod.not = icmp ne i32 %xtraiter, 0
  %21 = and i1 %cmp643, %lcmp.mod.not
  br i1 %21, label %for.body8.lr.ph.epil, label %for.cond.cleanup3

for.body8.lr.ph.epil:                             ; preds = %for.cond.cleanup3.loopexit.unr-lcssa
  %arrayidx18.epil = getelementptr inbounds i32, i32* %arrayidx16, i64 %indvars.iv52.unr
  %arrayidx18.promoted.epil = load i32, i32* %arrayidx18.epil, align 4, !tbaa !3
  %wide.trip.count.epil = zext i32 %l to i64
  br label %for.body8.epil

for.body8.epil:                                   ; preds = %for.body8.epil, %for.body8.lr.ph.epil
  %indvars.iv.epil = phi i64 [ 0, %for.body8.lr.ph.epil ], [ %indvars.iv.next.epil, %for.body8.epil ]
  %add51.epil = phi i32 [ %arrayidx18.promoted.epil, %for.body8.lr.ph.epil ], [ %add.epil, %for.body8.epil ]
  %arrayidx10.epil = getelementptr inbounds i32, i32* %arrayidx, i64 %indvars.iv.epil
  %22 = load i32, i32* %arrayidx10.epil, align 4, !tbaa !3
  %23 = mul nuw nsw i64 %indvars.iv.epil, %1
  %arrayidx12.epil = getelementptr inbounds i32, i32* %B, i64 %indvars.iv52.unr
  %arrayidx14.epil = getelementptr inbounds i32, i32* %arrayidx12.epil, i64 %23
  %24 = load i32, i32* %arrayidx14.epil, align 4, !tbaa !3
  %mul.epil = mul nsw i32 %24, %22
  %add.epil = add nsw i32 %add51.epil, %mul.epil
  %indvars.iv.next.epil = add nuw nsw i64 %indvars.iv.epil, 1
  %exitcond.epil.not = icmp eq i64 %indvars.iv.next.epil, %wide.trip.count.epil
  br i1 %exitcond.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil, label %for.body8.epil, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.epil:       ; preds = %for.body8.epil
  store i32 %add.epil, i32* %arrayidx18.epil, align 4, !tbaa !3
  br label %for.cond.cleanup3

for.cond.cleanup3:                                ; preds = %for.cond.cleanup3.loopexit.unr-lcssa, %for.cond5.for.cond.cleanup7_crit_edge.epil, %for.cond1.preheader
  %indvars.iv.next57 = or i64 %indvars.iv56, 1
  br i1 %cmp245, label %for.cond5.preheader.lr.ph.1, label %for.cond.cleanup3.1

for.cond5.for.cond.cleanup7_crit_edge:            ; preds = %for.body8
  store i32 %add, i32* %arrayidx18, align 4, !tbaa !3
  br label %for.cond.cleanup7

for.cond.cleanup7:                                ; preds = %for.cond5.for.cond.cleanup7_crit_edge, %for.cond5.preheader
  %indvars.iv.next53 = or i64 %indvars.iv52, 1
  br i1 %cmp643, label %for.body8.lr.ph.1, label %for.cond.cleanup7.1

body1:                                        ; preds = %for.body8.lr.ph, %for.body8
  %indvars.iv = phi i64 [ 0, %for.body8.lr.ph ], [ %indvars.iv.next, %body1 ]
  %add51 = phi i32 [ %arrayidx18.promoted, %for.body8.lr.ph ], [ %add, %body1 ]
  %arrayidx10 = getelementptr inbounds i32, i32* %arrayidx, i64 %indvars.iv
  %25 = load i32, i32* %arrayidx10, align 4, !tbaa !3
  %26 = mul nuw nsw i64 %indvars.iv, %1
  %arrayidx12 = getelementptr inbounds i32, i32* %B, i64 %indvars.iv52
  %arrayidx14 = getelementptr inbounds i32, i32* %arrayidx12, i64 %26
  %27 = load i32, i32* %arrayidx14, align 4, !tbaa !3
  %mul = mul nsw i32 %27, %25
  %add = add nsw i32 %add51, %mul
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1
  %exitcond.not = icmp eq i64 %indvars.iv.next, %wide.trip.count
  br i1 %exitcond.not, label %for.cond5.for.cond.cleanup7_crit_edge, label %body1, !llvm.loop !7

for.body8.lr.ph.1:                                ; preds = %for.cond.cleanup7
  %arrayidx18.1 = getelementptr inbounds i32, i32* %arrayidx16, i64 %indvars.iv.next53
  %arrayidx18.promoted.1 = load i32, i32* %arrayidx18.1, align 4, !tbaa !3
  %wide.trip.count.1 = zext i32 %l to i64
  br label %body2

body2:                                      ; preds = %body2, %for.body8.lr.ph.1
  %indvars.iv.1 = phi i64 [ 0, %for.body8.lr.ph.1 ], [ %indvars.iv.next.1, %body2 ]
  %add51.1 = phi i32 [ %arrayidx18.promoted.1, %for.body8.lr.ph.1 ], [ %add.1, %body2 ]
  %arrayidx10.1 = getelementptr inbounds i32, i32* %arrayidx, i64 %indvars.iv.1
  %28 = load i32, i32* %arrayidx10.1, align 4, !tbaa !3
  %29 = mul nuw nsw i64 %indvars.iv.1, %1
  %arrayidx12.1 = getelementptr inbounds i32, i32* %B, i64 %indvars.iv.next53
  %arrayidx14.1 = getelementptr inbounds i32, i32* %arrayidx12.1, i64 %29
  %30 = load i32, i32* %arrayidx14.1, align 4, !tbaa !3
  %mul.1 = mul nsw i32 %30, %28
  %add.1 = add nsw i32 %add51.1, %mul.1
  %indvars.iv.next.1 = add nuw nsw i64 %indvars.iv.1, 1
  %exitcond.1.not = icmp eq i64 %indvars.iv.next.1, %wide.trip.count.1
  br i1 %exitcond.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.1, label %body2, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.1:          ; preds = %for.body8.1
  store i32 %add.1, i32* %arrayidx18.1, align 4, !tbaa !3
  br label %for.cond.cleanup7.1

for.cond.cleanup7.1:                              ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1, %for.cond.cleanup7
  %indvars.iv.next53.1 = add nuw nsw i64 %indvars.iv52, 2
  %niter.nsub.1 = add i32 %niter, -2
  %niter.ncmp.1.not = icmp eq i32 %niter.nsub.1, 0
  br i1 %niter.ncmp.1.not, label %for.cond.cleanup3.loopexit.unr-lcssa, label %for.cond5.preheader, !llvm.loop !10

for.cond5.preheader.lr.ph.1:                      ; preds = %for.cond.cleanup3
  %31 = mul nuw nsw i64 %indvars.iv.next57, %0
  %arrayidx.1 = getelementptr inbounds i32, i32* %A, i64 %31
  %32 = mul nuw nsw i64 %indvars.iv.next57, %1
  %arrayidx16.1 = getelementptr inbounds i32, i32* %C, i64 %32
  %xtraiter.1 = and i32 %m, 1
  %33 = icmp eq i32 %2, 0
  br i1 %33, label %for.cond.cleanup3.loopexit.unr-lcssa.1, label %for.cond5.preheader.lr.ph.new.1

for.cond5.preheader.lr.ph.new.1:                  ; preds = %for.cond5.preheader.lr.ph.1
  %unroll_iter.1 = and i32 %m, -2
  br label %for.cond5.preheader.1

for.cond5.preheader.1:                            ; preds = %for.cond.cleanup7.1.1, %for.cond5.preheader.lr.ph.new.1
  %indvars.iv52.1 = phi i64 [ 0, %for.cond5.preheader.lr.ph.new.1 ], [ %indvars.iv.next53.1.1, %for.cond.cleanup7.1.1 ]
  %niter.1 = phi i32 [ %unroll_iter.1, %for.cond5.preheader.lr.ph.new.1 ], [ %niter.nsub.1.1, %for.cond.cleanup7.1.1 ]
  br i1 %cmp643, label %for.body8.lr.ph.187, label %for.cond.cleanup7.1102

for.body8.lr.ph.187:                              ; preds = %for.cond5.preheader.1
  %arrayidx18.184 = getelementptr inbounds i32, i32* %arrayidx16.1, i64 %indvars.iv52.1
  %arrayidx18.promoted.185 = load i32, i32* %arrayidx18.184, align 4, !tbaa !3
  %wide.trip.count.186 = zext i32 %l to i64
  br label %body3

body3:                                    ; preds = %for.body8.197, %for.body8.lr.ph.187
  %indvars.iv.188 = phi i64 [ 0, %for.body8.lr.ph.187 ], [ %indvars.iv.next.195, %body3 ]
  %add51.189 = phi i32 [ %arrayidx18.promoted.185, %for.body8.lr.ph.187 ], [ %add.194, %body3 ]
  %arrayidx10.190 = getelementptr inbounds i32, i32* %arrayidx.1, i64 %indvars.iv.188
  %34 = load i32, i32* %arrayidx10.190, align 4, !tbaa !3
  %35 = mul nuw nsw i64 %indvars.iv.188, %1
  %arrayidx12.191 = getelementptr inbounds i32, i32* %B, i64 %indvars.iv52.1
  %arrayidx14.192 = getelementptr inbounds i32, i32* %arrayidx12.191, i64 %35
  %36 = load i32, i32* %arrayidx14.192, align 4, !tbaa !3
  %mul.193 = mul nsw i32 %36, %34
  %add.194 = add nsw i32 %add51.189, %mul.193
  %indvars.iv.next.195 = add nuw nsw i64 %indvars.iv.188, 1
  %exitcond.196.not = icmp eq i64 %indvars.iv.next.195, %wide.trip.count.186
  br i1 %exitcond.196.not, label %for.cond5.for.cond.cleanup7_crit_edge.199, label %body3, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.199:        ; preds = %body3
  store i32 %add.194, i32* %arrayidx18.184, align 4, !tbaa !3
  br label %for.cond.cleanup7.1102

for.cond.cleanup7.1102:                           ; preds = %for.cond5.for.cond.cleanup7_crit_edge.199, %for.cond5.preheader.1
  %indvars.iv.next53.1100 = or i64 %indvars.iv52.1, 1
  br i1 %cmp643, label %for.body8.lr.ph.1.1, label %for.cond.cleanup7.1.1

for.body8.lr.ph.1.1:                              ; preds = %for.cond.cleanup7.1102
  %arrayidx18.1.1 = getelementptr inbounds i32, i32* %arrayidx16.1, i64 %indvars.iv.next53.1100
  %arrayidx18.promoted.1.1 = load i32, i32* %arrayidx18.1.1, align 4, !tbaa !3
  %wide.trip.count.1.1 = zext i32 %l to i64
  br label %body4

body4:                                    ; preds = %body4, %for.body8.lr.ph.1.1
  %indvars.iv.1.1 = phi i64 [ 0, %for.body8.lr.ph.1.1 ], [ %indvars.iv.next.1.1, %body4 ]
  %add51.1.1 = phi i32 [ %arrayidx18.promoted.1.1, %for.body8.lr.ph.1.1 ], [ %add.1.1, %body4 ]
  %arrayidx10.1.1 = getelementptr inbounds i32, i32* %arrayidx.1, i64 %indvars.iv.1.1
  %37 = load i32, i32* %arrayidx10.1.1, align 4, !tbaa !3
  %38 = mul nuw nsw i64 %indvars.iv.1.1, %1
  %arrayidx12.1.1 = getelementptr inbounds i32, i32* %B, i64 %indvars.iv.next53.1100
  %arrayidx14.1.1 = getelementptr inbounds i32, i32* %arrayidx12.1.1, i64 %38
  %39 = load i32, i32* %arrayidx14.1.1, align 4, !tbaa !3
  %mul.1.1 = mul nsw i32 %39, %37
  %add.1.1 = add nsw i32 %add51.1.1, %mul.1.1
  %indvars.iv.next.1.1 = add nuw nsw i64 %indvars.iv.1.1, 1
  %exitcond.1.1.not = icmp eq i64 %indvars.iv.next.1.1, %wide.trip.count.1.1
  br i1 %exitcond.1.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.1, label %body4, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.1.1:        ; preds = %body4
  store i32 %add.1.1, i32* %arrayidx18.1.1, align 4, !tbaa !3
  br label %for.cond.cleanup7.1.1

for.cond.cleanup7.1.1:                            ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.1, %for.cond.cleanup7.1102
  %indvars.iv.next53.1.1 = add nuw nsw i64 %indvars.iv52.1, 2
  %niter.nsub.1.1 = add i32 %niter.1, -2
  %niter.ncmp.1.1.not = icmp eq i32 %niter.nsub.1.1, 0
  br i1 %niter.ncmp.1.1.not, label %for.cond.cleanup3.loopexit.unr-lcssa.1, label %for.cond5.preheader.1, !llvm.loop !10

for.cond.cleanup3.loopexit.unr-lcssa.1:           ; preds = %for.cond.cleanup7.1.1, %for.cond5.preheader.lr.ph.1
  %indvars.iv52.unr.1 = phi i64 [ 0, %for.cond5.preheader.lr.ph.1 ], [ %indvars.iv.next53.1.1, %for.cond.cleanup7.1.1 ]
  %lcmp.mod.1.not = icmp ne i32 %xtraiter.1, 0
  %40 = and i1 %cmp643, %lcmp.mod.1.not
  br i1 %40, label %for.body8.lr.ph.epil.1, label %for.cond.cleanup3.1

for.body8.lr.ph.epil.1:                           ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.1
  %arrayidx18.epil.1 = getelementptr inbounds i32, i32* %arrayidx16.1, i64 %indvars.iv52.unr.1
  %arrayidx18.promoted.epil.1 = load i32, i32* %arrayidx18.epil.1, align 4, !tbaa !3
  %wide.trip.count.epil.1 = zext i32 %l to i64
  br label %for.body8.epil.1

for.body8.epil.1:                                 ; preds = %for.body8.epil.1, %for.body8.lr.ph.epil.1
  %indvars.iv.epil.1 = phi i64 [ 0, %for.body8.lr.ph.epil.1 ], [ %indvars.iv.next.epil.1, %for.body8.epil.1 ]
  %add51.epil.1 = phi i32 [ %arrayidx18.promoted.epil.1, %for.body8.lr.ph.epil.1 ], [ %add.epil.1, %for.body8.epil.1 ]
  %arrayidx10.epil.1 = getelementptr inbounds i32, i32* %arrayidx.1, i64 %indvars.iv.epil.1
  %41 = load i32, i32* %arrayidx10.epil.1, align 4, !tbaa !3
  %42 = mul nuw nsw i64 %indvars.iv.epil.1, %1
  %arrayidx12.epil.1 = getelementptr inbounds i32, i32* %B, i64 %indvars.iv52.unr.1
  %arrayidx14.epil.1 = getelementptr inbounds i32, i32* %arrayidx12.epil.1, i64 %42
  %43 = load i32, i32* %arrayidx14.epil.1, align 4, !tbaa !3
  %mul.epil.1 = mul nsw i32 %43, %41
  %add.epil.1 = add nsw i32 %add51.epil.1, %mul.epil.1
  %indvars.iv.next.epil.1 = add nuw nsw i64 %indvars.iv.epil.1, 1
  %exitcond.epil.1.not = icmp eq i64 %indvars.iv.next.epil.1, %wide.trip.count.epil.1
  br i1 %exitcond.epil.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.1, label %for.body8.epil.1, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.epil.1:     ; preds = %for.body8.epil.1
  store i32 %add.epil.1, i32* %arrayidx18.epil.1, align 4, !tbaa !3
  br label %for.cond.cleanup3.1

for.cond.cleanup3.1:                              ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.1, %for.cond5.for.cond.cleanup7_crit_edge.epil.1, %for.cond.cleanup3
  %indvars.iv.next57.1 = add nuw nsw i64 %indvars.iv56, 2
  %niter83.nsub.1 = add i32 %niter83, -2
  %niter83.ncmp.1.not = icmp eq i32 %niter83.nsub.1, 0
  br i1 %niter83.ncmp.1.not, label %for.cond.cleanup.loopexit.unr-lcssa, label %for.cond1.preheader, !llvm.loop !11
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

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
!11 = distinct !{!11, !8, !9}
