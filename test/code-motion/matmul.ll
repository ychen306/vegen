; RUN: %opt -test-code-motion -gather -inst-group=STORE:add.lcssa,STORE:add.lcssa.1 %s
; ModuleID = 'matmul.ll'
source_filename = "matmul.ll"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

; Function Attrs: nofree norecurse nounwind ssp uwtable
define dso_local void @foo(i32 %n, float* noalias nocapture readonly %a, float* noalias nocapture readonly %b, float* noalias nocapture %c) local_unnamed_addr #0 {
entry:
  %0 = zext i32 %n to i64
  %cmp50 = icmp sgt i32 %n, 0
  br i1 %cmp50, label %for.cond1.preheader.lr.ph, label %for.cond.cleanup

for.cond1.preheader.lr.ph:                        ; preds = %entry
  %1 = add i32 %n, -1
  %xtraiter97 = and i32 %n, 3
  %2 = icmp ult i32 %1, 3
  br i1 %2, label %for.cond.cleanup.loopexit.unr-lcssa, label %for.cond1.preheader.lr.ph.new

for.cond1.preheader.lr.ph.new:                    ; preds = %for.cond1.preheader.lr.ph
  %unroll_iter170 = and i32 %n, -4
  br label %for.cond1.preheader

for.cond1.preheader:                              ; preds = %for.cond.cleanup3.3, %for.cond1.preheader.lr.ph.new
  %indvars.iv94 = phi i64 [ 0, %for.cond1.preheader.lr.ph.new ], [ %indvars.iv.next95.3, %for.cond.cleanup3.3 ]
  %niter171 = phi i32 [ %unroll_iter170, %for.cond1.preheader.lr.ph.new ], [ %niter171.nsub.3, %for.cond.cleanup3.3 ]
  %3 = mul nuw nsw i64 %indvars.iv94, %0
  %arrayidx = getelementptr inbounds float, float* %a, i64 %3
  %arrayidx16 = getelementptr inbounds float, float* %c, i64 %3
  %xtraiter58 = and i32 %n, 3
  %4 = icmp ult i32 %1, 3
  br i1 %4, label %for.cond.cleanup3.loopexit.unr-lcssa, label %for.cond5.preheader.lr.ph.new

for.cond5.preheader.lr.ph.new:                    ; preds = %for.cond1.preheader
  %unroll_iter71 = and i32 %n, -4
  br label %for.cond5.preheader

for.cond.cleanup.loopexit.unr-lcssa.loopexit:     ; preds = %for.cond.cleanup3.3
  %indvars.iv.next95.3.lcssa = phi i64 [ %indvars.iv.next95.3, %for.cond.cleanup3.3 ]
  br label %for.cond.cleanup.loopexit.unr-lcssa

for.cond.cleanup.loopexit.unr-lcssa:              ; preds = %for.cond.cleanup.loopexit.unr-lcssa.loopexit, %for.cond1.preheader.lr.ph
  %indvars.iv94.unr = phi i64 [ 0, %for.cond1.preheader.lr.ph ], [ %indvars.iv.next95.3.lcssa, %for.cond.cleanup.loopexit.unr-lcssa.loopexit ]
  %lcmp.mod169.not = icmp eq i32 %xtraiter97, 0
  br i1 %lcmp.mod169.not, label %for.cond.cleanup, label %for.cond1.preheader.epil.preheader

for.cond1.preheader.epil.preheader:               ; preds = %for.cond.cleanup.loopexit.unr-lcssa
  br label %for.cond1.preheader.epil

for.cond1.preheader.epil:                         ; preds = %for.cond1.preheader.epil.preheader, %for.cond.cleanup3.epil
  %indvars.iv94.epil = phi i64 [ %indvars.iv.next95.epil, %for.cond.cleanup3.epil ], [ %indvars.iv94.unr, %for.cond1.preheader.epil.preheader ]
  %epil.iter168 = phi i32 [ %epil.iter168.sub, %for.cond.cleanup3.epil ], [ %xtraiter97, %for.cond1.preheader.epil.preheader ]
  %5 = mul nuw nsw i64 %indvars.iv94.epil, %0
  %arrayidx.epil = getelementptr inbounds float, float* %a, i64 %5
  %arrayidx16.epil = getelementptr inbounds float, float* %c, i64 %5
  %xtraiter58.epil = and i32 %n, 3
  %6 = icmp ult i32 %1, 3
  br i1 %6, label %for.cond.cleanup3.loopexit.unr-lcssa.epil, label %for.cond5.preheader.lr.ph.new.epil

for.cond5.preheader.lr.ph.new.epil:               ; preds = %for.cond1.preheader.epil
  %unroll_iter71.epil = and i32 %n, -4
  br label %for.cond5.preheader.epil98

for.cond5.preheader.epil98:                       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.epil, %for.cond5.preheader.lr.ph.new.epil
  %indvars.iv55.epil99 = phi i64 [ 0, %for.cond5.preheader.lr.ph.new.epil ], [ %indvars.iv.next56.3.epil, %for.cond5.for.cond.cleanup7_crit_edge.3.epil ]
  %niter72.epil = phi i32 [ %unroll_iter71.epil, %for.cond5.preheader.lr.ph.new.epil ], [ %niter72.nsub.3.epil, %for.cond5.for.cond.cleanup7_crit_edge.3.epil ]
  %arrayidx18.epil101 = getelementptr inbounds float, float* %arrayidx16.epil, i64 %indvars.iv55.epil99
  %arrayidx18.promoted.epil102 = load float, float* %arrayidx18.epil101, align 4, !tbaa !3
  %xtraiter.epil104 = and i32 %n, 3
  %7 = icmp ult i32 %1, 3
  br i1 %7, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144, label %for.body8.lr.ph.new.epil105

for.body8.lr.ph.new.epil105:                      ; preds = %for.cond5.preheader.epil98
  %unroll_iter.epil106 = and i32 %n, -4
  br label %for.body8.epil107

for.body8.epil107:                                ; preds = %for.body8.epil107, %for.body8.lr.ph.new.epil105
  %indvars.iv.epil108 = phi i64 [ 0, %for.body8.lr.ph.new.epil105 ], [ %indvars.iv.next.3.epil137, %for.body8.epil107 ]
  %add53.epil109 = phi float [ %arrayidx18.promoted.epil102, %for.body8.lr.ph.new.epil105 ], [ %add.3.epil136, %for.body8.epil107 ]
  %niter.epil110 = phi i32 [ %unroll_iter.epil106, %for.body8.lr.ph.new.epil105 ], [ %niter.nsub.3.epil138, %for.body8.epil107 ]
  %arrayidx10.epil111 = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.epil108
  %8 = load float, float* %arrayidx10.epil111, align 4, !tbaa !3
  %9 = mul nuw nsw i64 %indvars.iv.epil108, %0
  %arrayidx12.epil112 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil99
  %arrayidx14.epil113 = getelementptr inbounds float, float* %arrayidx12.epil112, i64 %9
  %10 = load float, float* %arrayidx14.epil113, align 4, !tbaa !3
  %mul.epil114 = fmul float %8, %10
  %add.epil115 = fadd float %add53.epil109, %mul.epil114
  %indvars.iv.next.epil116 = or i64 %indvars.iv.epil108, 1
  %arrayidx10.1.epil118 = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.epil116
  %11 = load float, float* %arrayidx10.1.epil118, align 4, !tbaa !3
  %12 = mul nuw nsw i64 %indvars.iv.next.epil116, %0
  %arrayidx12.1.epil119 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil99
  %arrayidx14.1.epil120 = getelementptr inbounds float, float* %arrayidx12.1.epil119, i64 %12
  %13 = load float, float* %arrayidx14.1.epil120, align 4, !tbaa !3
  %mul.1.epil121 = fmul float %11, %13
  %add.1.epil122 = fadd float %add.epil115, %mul.1.epil121
  %indvars.iv.next.1.epil123 = or i64 %indvars.iv.epil108, 2
  %arrayidx10.2.epil125 = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.1.epil123
  %14 = load float, float* %arrayidx10.2.epil125, align 4, !tbaa !3
  %15 = mul nuw nsw i64 %indvars.iv.next.1.epil123, %0
  %arrayidx12.2.epil126 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil99
  %arrayidx14.2.epil127 = getelementptr inbounds float, float* %arrayidx12.2.epil126, i64 %15
  %16 = load float, float* %arrayidx14.2.epil127, align 4, !tbaa !3
  %mul.2.epil128 = fmul float %14, %16
  %add.2.epil129 = fadd float %add.1.epil122, %mul.2.epil128
  %indvars.iv.next.2.epil130 = or i64 %indvars.iv.epil108, 3
  %arrayidx10.3.epil132 = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.2.epil130
  %17 = load float, float* %arrayidx10.3.epil132, align 4, !tbaa !3
  %18 = mul nuw nsw i64 %indvars.iv.next.2.epil130, %0
  %arrayidx12.3.epil133 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil99
  %arrayidx14.3.epil134 = getelementptr inbounds float, float* %arrayidx12.3.epil133, i64 %18
  %19 = load float, float* %arrayidx14.3.epil134, align 4, !tbaa !3
  %mul.3.epil135 = fmul float %17, %19
  %add.3.epil136 = fadd float %add.2.epil129, %mul.3.epil135
  %indvars.iv.next.3.epil137 = add nuw nsw i64 %indvars.iv.epil108, 4
  %niter.nsub.3.epil138 = add i32 %niter.epil110, -4
  %niter.ncmp.3.epil139.not = icmp eq i32 %niter.nsub.3.epil138, 0
  br i1 %niter.ncmp.3.epil139.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144.loopexit, label %for.body8.epil107, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144.loopexit: ; preds = %for.body8.epil107
  %add.3.epil136.lcssa = phi float [ %add.3.epil136, %for.body8.epil107 ]
  %indvars.iv.next.3.epil137.lcssa = phi i64 [ %indvars.iv.next.3.epil137, %for.body8.epil107 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144.loopexit, %for.cond5.preheader.epil98
  %add.lcssa.ph.epil145 = phi float [ undef, %for.cond5.preheader.epil98 ], [ %add.3.epil136.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144.loopexit ]
  %indvars.iv.unr.epil146 = phi i64 [ 0, %for.cond5.preheader.epil98 ], [ %indvars.iv.next.3.epil137.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144.loopexit ]
  %add53.unr.epil147 = phi float [ %arrayidx18.promoted.epil102, %for.cond5.preheader.epil98 ], [ %add.3.epil136.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144.loopexit ]
  %lcmp.mod.epil148.not = icmp eq i32 %xtraiter.epil104, 0
  br i1 %lcmp.mod.epil148.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil164, label %for.body8.epil.epil150.preheader

for.body8.epil.epil150.preheader:                 ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144
  br label %for.body8.epil.epil150

for.body8.epil.epil150:                           ; preds = %for.body8.epil.epil150.preheader, %for.body8.epil.epil150
  %indvars.iv.epil.epil151 = phi i64 [ %indvars.iv.next.epil.epil159, %for.body8.epil.epil150 ], [ %indvars.iv.unr.epil146, %for.body8.epil.epil150.preheader ]
  %add53.epil.epil152 = phi float [ %add.epil.epil158, %for.body8.epil.epil150 ], [ %add53.unr.epil147, %for.body8.epil.epil150.preheader ]
  %epil.iter.epil153 = phi i32 [ %epil.iter.sub.epil160, %for.body8.epil.epil150 ], [ %xtraiter.epil104, %for.body8.epil.epil150.preheader ]
  %arrayidx10.epil.epil154 = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.epil.epil151
  %20 = load float, float* %arrayidx10.epil.epil154, align 4, !tbaa !3
  %21 = mul nuw nsw i64 %indvars.iv.epil.epil151, %0
  %arrayidx12.epil.epil155 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil99
  %arrayidx14.epil.epil156 = getelementptr inbounds float, float* %arrayidx12.epil.epil155, i64 %21
  %22 = load float, float* %arrayidx14.epil.epil156, align 4, !tbaa !3
  %mul.epil.epil157 = fmul float %20, %22
  %add.epil.epil158 = fadd float %add53.epil.epil152, %mul.epil.epil157
  %indvars.iv.next.epil.epil159 = add nuw nsw i64 %indvars.iv.epil.epil151, 1
  %epil.iter.sub.epil160 = add i32 %epil.iter.epil153, -1
  %epil.iter.cmp.epil161.not = icmp eq i32 %epil.iter.sub.epil160, 0
  br i1 %epil.iter.cmp.epil161.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil164.loopexit, label %for.body8.epil.epil150, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.epil164.loopexit: ; preds = %for.body8.epil.epil150
  %add.epil.epil158.lcssa = phi float [ %add.epil.epil158, %for.body8.epil.epil150 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.epil164

for.cond5.for.cond.cleanup7_crit_edge.epil164:    ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil164.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144
  %add.lcssa.epil165 = phi float [ %add.lcssa.ph.epil145, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil144 ], [ %add.epil.epil158.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.epil164.loopexit ]
  store float %add.lcssa.epil165, float* %arrayidx18.epil101, align 4, !tbaa !3
  %indvars.iv.next56.epil167 = or i64 %indvars.iv55.epil99, 1
  %arrayidx18.1.epil = getelementptr inbounds float, float* %arrayidx16.epil, i64 %indvars.iv.next56.epil167
  %arrayidx18.promoted.1.epil = load float, float* %arrayidx18.1.epil, align 4, !tbaa !3
  %xtraiter.1.epil = and i32 %n, 3
  %23 = icmp ult i32 %1, 3
  br i1 %23, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil, label %for.body8.lr.ph.new.1.epil

for.body8.lr.ph.new.1.epil:                       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil164
  %unroll_iter.1.epil = and i32 %n, -4
  br label %for.body8.1.epil

for.body8.1.epil:                                 ; preds = %for.body8.1.epil, %for.body8.lr.ph.new.1.epil
  %indvars.iv.1.epil = phi i64 [ 0, %for.body8.lr.ph.new.1.epil ], [ %indvars.iv.next.3.1.epil, %for.body8.1.epil ]
  %add53.1.epil = phi float [ %arrayidx18.promoted.1.epil, %for.body8.lr.ph.new.1.epil ], [ %add.3.1.epil, %for.body8.1.epil ]
  %niter.1.epil = phi i32 [ %unroll_iter.1.epil, %for.body8.lr.ph.new.1.epil ], [ %niter.nsub.3.1.epil, %for.body8.1.epil ]
  %arrayidx10.173.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.1.epil
  %24 = load float, float* %arrayidx10.173.epil, align 4, !tbaa !3
  %25 = mul nuw nsw i64 %indvars.iv.1.epil, %0
  %arrayidx12.174.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.epil167
  %arrayidx14.175.epil = getelementptr inbounds float, float* %arrayidx12.174.epil, i64 %25
  %26 = load float, float* %arrayidx14.175.epil, align 4, !tbaa !3
  %mul.176.epil = fmul float %24, %26
  %add.177.epil = fadd float %add53.1.epil, %mul.176.epil
  %indvars.iv.next.178.epil = or i64 %indvars.iv.1.epil, 1
  %arrayidx10.1.1.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.178.epil
  %27 = load float, float* %arrayidx10.1.1.epil, align 4, !tbaa !3
  %28 = mul nuw nsw i64 %indvars.iv.next.178.epil, %0
  %arrayidx12.1.1.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.epil167
  %arrayidx14.1.1.epil = getelementptr inbounds float, float* %arrayidx12.1.1.epil, i64 %28
  %29 = load float, float* %arrayidx14.1.1.epil, align 4, !tbaa !3
  %mul.1.1.epil = fmul float %27, %29
  %add.1.1.epil = fadd float %add.177.epil, %mul.1.1.epil
  %indvars.iv.next.1.1.epil = or i64 %indvars.iv.1.epil, 2
  %arrayidx10.2.1.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.1.1.epil
  %30 = load float, float* %arrayidx10.2.1.epil, align 4, !tbaa !3
  %31 = mul nuw nsw i64 %indvars.iv.next.1.1.epil, %0
  %arrayidx12.2.1.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.epil167
  %arrayidx14.2.1.epil = getelementptr inbounds float, float* %arrayidx12.2.1.epil, i64 %31
  %32 = load float, float* %arrayidx14.2.1.epil, align 4, !tbaa !3
  %mul.2.1.epil = fmul float %30, %32
  %add.2.1.epil = fadd float %add.1.1.epil, %mul.2.1.epil
  %indvars.iv.next.2.1.epil = or i64 %indvars.iv.1.epil, 3
  %arrayidx10.3.1.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.2.1.epil
  %33 = load float, float* %arrayidx10.3.1.epil, align 4, !tbaa !3
  %34 = mul nuw nsw i64 %indvars.iv.next.2.1.epil, %0
  %arrayidx12.3.1.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.epil167
  %arrayidx14.3.1.epil = getelementptr inbounds float, float* %arrayidx12.3.1.epil, i64 %34
  %35 = load float, float* %arrayidx14.3.1.epil, align 4, !tbaa !3
  %mul.3.1.epil = fmul float %33, %35
  %add.3.1.epil = fadd float %add.2.1.epil, %mul.3.1.epil
  %indvars.iv.next.3.1.epil = add nuw nsw i64 %indvars.iv.1.epil, 4
  %niter.nsub.3.1.epil = add i32 %niter.1.epil, -4
  %niter.ncmp.3.1.epil.not = icmp eq i32 %niter.nsub.3.1.epil, 0
  br i1 %niter.ncmp.3.1.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil.loopexit, label %for.body8.1.epil, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil.loopexit: ; preds = %for.body8.1.epil
  %add.3.1.epil.lcssa = phi float [ %add.3.1.epil, %for.body8.1.epil ]
  %indvars.iv.next.3.1.epil.lcssa = phi i64 [ %indvars.iv.next.3.1.epil, %for.body8.1.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.epil164
  %add.lcssa.ph.1.epil = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.epil164 ], [ %add.3.1.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil.loopexit ]
  %indvars.iv.unr.1.epil = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.epil164 ], [ %indvars.iv.next.3.1.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil.loopexit ]
  %add53.unr.1.epil = phi float [ %arrayidx18.promoted.1.epil, %for.cond5.for.cond.cleanup7_crit_edge.epil164 ], [ %add.3.1.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil.loopexit ]
  %lcmp.mod.1.epil.not = icmp eq i32 %xtraiter.1.epil, 0
  br i1 %lcmp.mod.1.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.epil, label %for.body8.epil.1.epil.preheader

for.body8.epil.1.epil.preheader:                  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil
  br label %for.body8.epil.1.epil

for.body8.epil.1.epil:                            ; preds = %for.body8.epil.1.epil.preheader, %for.body8.epil.1.epil
  %indvars.iv.epil.1.epil = phi i64 [ %indvars.iv.next.epil.1.epil, %for.body8.epil.1.epil ], [ %indvars.iv.unr.1.epil, %for.body8.epil.1.epil.preheader ]
  %add53.epil.1.epil = phi float [ %add.epil.1.epil, %for.body8.epil.1.epil ], [ %add53.unr.1.epil, %for.body8.epil.1.epil.preheader ]
  %epil.iter.1.epil = phi i32 [ %epil.iter.sub.1.epil, %for.body8.epil.1.epil ], [ %xtraiter.1.epil, %for.body8.epil.1.epil.preheader ]
  %arrayidx10.epil.1.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.epil.1.epil
  %36 = load float, float* %arrayidx10.epil.1.epil, align 4, !tbaa !3
  %37 = mul nuw nsw i64 %indvars.iv.epil.1.epil, %0
  %arrayidx12.epil.1.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.epil167
  %arrayidx14.epil.1.epil = getelementptr inbounds float, float* %arrayidx12.epil.1.epil, i64 %37
  %38 = load float, float* %arrayidx14.epil.1.epil, align 4, !tbaa !3
  %mul.epil.1.epil = fmul float %36, %38
  %add.epil.1.epil = fadd float %add53.epil.1.epil, %mul.epil.1.epil
  %indvars.iv.next.epil.1.epil = add nuw nsw i64 %indvars.iv.epil.1.epil, 1
  %epil.iter.sub.1.epil = add i32 %epil.iter.1.epil, -1
  %epil.iter.cmp.1.epil.not = icmp eq i32 %epil.iter.sub.1.epil, 0
  br i1 %epil.iter.cmp.1.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.epil.loopexit, label %for.body8.epil.1.epil, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.1.epil.loopexit: ; preds = %for.body8.epil.1.epil
  %add.epil.1.epil.lcssa = phi float [ %add.epil.1.epil, %for.body8.epil.1.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.1.epil

for.cond5.for.cond.cleanup7_crit_edge.1.epil:     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.epil.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil
  %add.lcssa.1.epil = phi float [ %add.lcssa.ph.1.epil, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.epil ], [ %add.epil.1.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.1.epil.loopexit ]
  store float %add.lcssa.1.epil, float* %arrayidx18.1.epil, align 4, !tbaa !3
  %indvars.iv.next56.1.epil = or i64 %indvars.iv55.epil99, 2
  %arrayidx18.2.epil = getelementptr inbounds float, float* %arrayidx16.epil, i64 %indvars.iv.next56.1.epil
  %arrayidx18.promoted.2.epil = load float, float* %arrayidx18.2.epil, align 4, !tbaa !3
  %xtraiter.2.epil = and i32 %n, 3
  %39 = icmp ult i32 %1, 3
  br i1 %39, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil, label %for.body8.lr.ph.new.2.epil

for.body8.lr.ph.new.2.epil:                       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.epil
  %unroll_iter.2.epil = and i32 %n, -4
  br label %for.body8.2.epil

for.body8.2.epil:                                 ; preds = %for.body8.2.epil, %for.body8.lr.ph.new.2.epil
  %indvars.iv.2.epil = phi i64 [ 0, %for.body8.lr.ph.new.2.epil ], [ %indvars.iv.next.3.2.epil, %for.body8.2.epil ]
  %add53.2.epil = phi float [ %arrayidx18.promoted.2.epil, %for.body8.lr.ph.new.2.epil ], [ %add.3.2.epil, %for.body8.2.epil ]
  %niter.2.epil = phi i32 [ %unroll_iter.2.epil, %for.body8.lr.ph.new.2.epil ], [ %niter.nsub.3.2.epil, %for.body8.2.epil ]
  %arrayidx10.280.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.2.epil
  %40 = load float, float* %arrayidx10.280.epil, align 4, !tbaa !3
  %41 = mul nuw nsw i64 %indvars.iv.2.epil, %0
  %arrayidx12.281.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.epil
  %arrayidx14.282.epil = getelementptr inbounds float, float* %arrayidx12.281.epil, i64 %41
  %42 = load float, float* %arrayidx14.282.epil, align 4, !tbaa !3
  %mul.283.epil = fmul float %40, %42
  %add.284.epil = fadd float %add53.2.epil, %mul.283.epil
  %indvars.iv.next.285.epil = or i64 %indvars.iv.2.epil, 1
  %arrayidx10.1.2.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.285.epil
  %43 = load float, float* %arrayidx10.1.2.epil, align 4, !tbaa !3
  %44 = mul nuw nsw i64 %indvars.iv.next.285.epil, %0
  %arrayidx12.1.2.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.epil
  %arrayidx14.1.2.epil = getelementptr inbounds float, float* %arrayidx12.1.2.epil, i64 %44
  %45 = load float, float* %arrayidx14.1.2.epil, align 4, !tbaa !3
  %mul.1.2.epil = fmul float %43, %45
  %add.1.2.epil = fadd float %add.284.epil, %mul.1.2.epil
  %indvars.iv.next.1.2.epil = or i64 %indvars.iv.2.epil, 2
  %arrayidx10.2.2.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.1.2.epil
  %46 = load float, float* %arrayidx10.2.2.epil, align 4, !tbaa !3
  %47 = mul nuw nsw i64 %indvars.iv.next.1.2.epil, %0
  %arrayidx12.2.2.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.epil
  %arrayidx14.2.2.epil = getelementptr inbounds float, float* %arrayidx12.2.2.epil, i64 %47
  %48 = load float, float* %arrayidx14.2.2.epil, align 4, !tbaa !3
  %mul.2.2.epil = fmul float %46, %48
  %add.2.2.epil = fadd float %add.1.2.epil, %mul.2.2.epil
  %indvars.iv.next.2.2.epil = or i64 %indvars.iv.2.epil, 3
  %arrayidx10.3.2.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.2.2.epil
  %49 = load float, float* %arrayidx10.3.2.epil, align 4, !tbaa !3
  %50 = mul nuw nsw i64 %indvars.iv.next.2.2.epil, %0
  %arrayidx12.3.2.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.epil
  %arrayidx14.3.2.epil = getelementptr inbounds float, float* %arrayidx12.3.2.epil, i64 %50
  %51 = load float, float* %arrayidx14.3.2.epil, align 4, !tbaa !3
  %mul.3.2.epil = fmul float %49, %51
  %add.3.2.epil = fadd float %add.2.2.epil, %mul.3.2.epil
  %indvars.iv.next.3.2.epil = add nuw nsw i64 %indvars.iv.2.epil, 4
  %niter.nsub.3.2.epil = add i32 %niter.2.epil, -4
  %niter.ncmp.3.2.epil.not = icmp eq i32 %niter.nsub.3.2.epil, 0
  br i1 %niter.ncmp.3.2.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil.loopexit, label %for.body8.2.epil, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil.loopexit: ; preds = %for.body8.2.epil
  %add.3.2.epil.lcssa = phi float [ %add.3.2.epil, %for.body8.2.epil ]
  %indvars.iv.next.3.2.epil.lcssa = phi i64 [ %indvars.iv.next.3.2.epil, %for.body8.2.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.1.epil
  %add.lcssa.ph.2.epil = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.1.epil ], [ %add.3.2.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil.loopexit ]
  %indvars.iv.unr.2.epil = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.1.epil ], [ %indvars.iv.next.3.2.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil.loopexit ]
  %add53.unr.2.epil = phi float [ %arrayidx18.promoted.2.epil, %for.cond5.for.cond.cleanup7_crit_edge.1.epil ], [ %add.3.2.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil.loopexit ]
  %lcmp.mod.2.epil.not = icmp eq i32 %xtraiter.2.epil, 0
  br i1 %lcmp.mod.2.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.2.epil, label %for.body8.epil.2.epil.preheader

for.body8.epil.2.epil.preheader:                  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil
  br label %for.body8.epil.2.epil

for.body8.epil.2.epil:                            ; preds = %for.body8.epil.2.epil.preheader, %for.body8.epil.2.epil
  %indvars.iv.epil.2.epil = phi i64 [ %indvars.iv.next.epil.2.epil, %for.body8.epil.2.epil ], [ %indvars.iv.unr.2.epil, %for.body8.epil.2.epil.preheader ]
  %add53.epil.2.epil = phi float [ %add.epil.2.epil, %for.body8.epil.2.epil ], [ %add53.unr.2.epil, %for.body8.epil.2.epil.preheader ]
  %epil.iter.2.epil = phi i32 [ %epil.iter.sub.2.epil, %for.body8.epil.2.epil ], [ %xtraiter.2.epil, %for.body8.epil.2.epil.preheader ]
  %arrayidx10.epil.2.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.epil.2.epil
  %52 = load float, float* %arrayidx10.epil.2.epil, align 4, !tbaa !3
  %53 = mul nuw nsw i64 %indvars.iv.epil.2.epil, %0
  %arrayidx12.epil.2.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.epil
  %arrayidx14.epil.2.epil = getelementptr inbounds float, float* %arrayidx12.epil.2.epil, i64 %53
  %54 = load float, float* %arrayidx14.epil.2.epil, align 4, !tbaa !3
  %mul.epil.2.epil = fmul float %52, %54
  %add.epil.2.epil = fadd float %add53.epil.2.epil, %mul.epil.2.epil
  %indvars.iv.next.epil.2.epil = add nuw nsw i64 %indvars.iv.epil.2.epil, 1
  %epil.iter.sub.2.epil = add i32 %epil.iter.2.epil, -1
  %epil.iter.cmp.2.epil.not = icmp eq i32 %epil.iter.sub.2.epil, 0
  br i1 %epil.iter.cmp.2.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.2.epil.loopexit, label %for.body8.epil.2.epil, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.2.epil.loopexit: ; preds = %for.body8.epil.2.epil
  %add.epil.2.epil.lcssa = phi float [ %add.epil.2.epil, %for.body8.epil.2.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.2.epil

for.cond5.for.cond.cleanup7_crit_edge.2.epil:     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2.epil.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil
  %add.lcssa.2.epil = phi float [ %add.lcssa.ph.2.epil, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.epil ], [ %add.epil.2.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.2.epil.loopexit ]
  store float %add.lcssa.2.epil, float* %arrayidx18.2.epil, align 4, !tbaa !3
  %indvars.iv.next56.2.epil = or i64 %indvars.iv55.epil99, 3
  %arrayidx18.3.epil = getelementptr inbounds float, float* %arrayidx16.epil, i64 %indvars.iv.next56.2.epil
  %arrayidx18.promoted.3.epil = load float, float* %arrayidx18.3.epil, align 4, !tbaa !3
  %xtraiter.3.epil = and i32 %n, 3
  %55 = icmp ult i32 %1, 3
  br i1 %55, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil, label %for.body8.lr.ph.new.3.epil

for.body8.lr.ph.new.3.epil:                       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2.epil
  %unroll_iter.3.epil = and i32 %n, -4
  br label %for.body8.3.epil

for.body8.3.epil:                                 ; preds = %for.body8.3.epil, %for.body8.lr.ph.new.3.epil
  %indvars.iv.3.epil = phi i64 [ 0, %for.body8.lr.ph.new.3.epil ], [ %indvars.iv.next.3.3.epil, %for.body8.3.epil ]
  %add53.3.epil = phi float [ %arrayidx18.promoted.3.epil, %for.body8.lr.ph.new.3.epil ], [ %add.3.3.epil, %for.body8.3.epil ]
  %niter.3.epil = phi i32 [ %unroll_iter.3.epil, %for.body8.lr.ph.new.3.epil ], [ %niter.nsub.3.3.epil, %for.body8.3.epil ]
  %arrayidx10.387.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.3.epil
  %56 = load float, float* %arrayidx10.387.epil, align 4, !tbaa !3
  %57 = mul nuw nsw i64 %indvars.iv.3.epil, %0
  %arrayidx12.388.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.epil
  %arrayidx14.389.epil = getelementptr inbounds float, float* %arrayidx12.388.epil, i64 %57
  %58 = load float, float* %arrayidx14.389.epil, align 4, !tbaa !3
  %mul.390.epil = fmul float %56, %58
  %add.391.epil = fadd float %add53.3.epil, %mul.390.epil
  %indvars.iv.next.392.epil = or i64 %indvars.iv.3.epil, 1
  %arrayidx10.1.3.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.392.epil
  %59 = load float, float* %arrayidx10.1.3.epil, align 4, !tbaa !3
  %60 = mul nuw nsw i64 %indvars.iv.next.392.epil, %0
  %arrayidx12.1.3.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.epil
  %arrayidx14.1.3.epil = getelementptr inbounds float, float* %arrayidx12.1.3.epil, i64 %60
  %61 = load float, float* %arrayidx14.1.3.epil, align 4, !tbaa !3
  %mul.1.3.epil = fmul float %59, %61
  %add.1.3.epil = fadd float %add.391.epil, %mul.1.3.epil
  %indvars.iv.next.1.3.epil = or i64 %indvars.iv.3.epil, 2
  %arrayidx10.2.3.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.1.3.epil
  %62 = load float, float* %arrayidx10.2.3.epil, align 4, !tbaa !3
  %63 = mul nuw nsw i64 %indvars.iv.next.1.3.epil, %0
  %arrayidx12.2.3.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.epil
  %arrayidx14.2.3.epil = getelementptr inbounds float, float* %arrayidx12.2.3.epil, i64 %63
  %64 = load float, float* %arrayidx14.2.3.epil, align 4, !tbaa !3
  %mul.2.3.epil = fmul float %62, %64
  %add.2.3.epil = fadd float %add.1.3.epil, %mul.2.3.epil
  %indvars.iv.next.2.3.epil = or i64 %indvars.iv.3.epil, 3
  %arrayidx10.3.3.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.2.3.epil
  %65 = load float, float* %arrayidx10.3.3.epil, align 4, !tbaa !3
  %66 = mul nuw nsw i64 %indvars.iv.next.2.3.epil, %0
  %arrayidx12.3.3.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.epil
  %arrayidx14.3.3.epil = getelementptr inbounds float, float* %arrayidx12.3.3.epil, i64 %66
  %67 = load float, float* %arrayidx14.3.3.epil, align 4, !tbaa !3
  %mul.3.3.epil = fmul float %65, %67
  %add.3.3.epil = fadd float %add.2.3.epil, %mul.3.3.epil
  %indvars.iv.next.3.3.epil = add nuw nsw i64 %indvars.iv.3.epil, 4
  %niter.nsub.3.3.epil = add i32 %niter.3.epil, -4
  %niter.ncmp.3.3.epil.not = icmp eq i32 %niter.nsub.3.3.epil, 0
  br i1 %niter.ncmp.3.3.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil.loopexit, label %for.body8.3.epil, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil.loopexit: ; preds = %for.body8.3.epil
  %add.3.3.epil.lcssa = phi float [ %add.3.3.epil, %for.body8.3.epil ]
  %indvars.iv.next.3.3.epil.lcssa = phi i64 [ %indvars.iv.next.3.3.epil, %for.body8.3.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.2.epil
  %add.lcssa.ph.3.epil = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.2.epil ], [ %add.3.3.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil.loopexit ]
  %indvars.iv.unr.3.epil = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.2.epil ], [ %indvars.iv.next.3.3.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil.loopexit ]
  %add53.unr.3.epil = phi float [ %arrayidx18.promoted.3.epil, %for.cond5.for.cond.cleanup7_crit_edge.2.epil ], [ %add.3.3.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil.loopexit ]
  %lcmp.mod.3.epil.not = icmp eq i32 %xtraiter.3.epil, 0
  br i1 %lcmp.mod.3.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.3.epil, label %for.body8.epil.3.epil.preheader

for.body8.epil.3.epil.preheader:                  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil
  br label %for.body8.epil.3.epil

for.body8.epil.3.epil:                            ; preds = %for.body8.epil.3.epil.preheader, %for.body8.epil.3.epil
  %indvars.iv.epil.3.epil = phi i64 [ %indvars.iv.next.epil.3.epil, %for.body8.epil.3.epil ], [ %indvars.iv.unr.3.epil, %for.body8.epil.3.epil.preheader ]
  %add53.epil.3.epil = phi float [ %add.epil.3.epil, %for.body8.epil.3.epil ], [ %add53.unr.3.epil, %for.body8.epil.3.epil.preheader ]
  %epil.iter.3.epil = phi i32 [ %epil.iter.sub.3.epil, %for.body8.epil.3.epil ], [ %xtraiter.3.epil, %for.body8.epil.3.epil.preheader ]
  %arrayidx10.epil.3.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.epil.3.epil
  %68 = load float, float* %arrayidx10.epil.3.epil, align 4, !tbaa !3
  %69 = mul nuw nsw i64 %indvars.iv.epil.3.epil, %0
  %arrayidx12.epil.3.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.epil
  %arrayidx14.epil.3.epil = getelementptr inbounds float, float* %arrayidx12.epil.3.epil, i64 %69
  %70 = load float, float* %arrayidx14.epil.3.epil, align 4, !tbaa !3
  %mul.epil.3.epil = fmul float %68, %70
  %add.epil.3.epil = fadd float %add53.epil.3.epil, %mul.epil.3.epil
  %indvars.iv.next.epil.3.epil = add nuw nsw i64 %indvars.iv.epil.3.epil, 1
  %epil.iter.sub.3.epil = add i32 %epil.iter.3.epil, -1
  %epil.iter.cmp.3.epil.not = icmp eq i32 %epil.iter.sub.3.epil, 0
  br i1 %epil.iter.cmp.3.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.3.epil.loopexit, label %for.body8.epil.3.epil, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.3.epil.loopexit: ; preds = %for.body8.epil.3.epil
  %add.epil.3.epil.lcssa = phi float [ %add.epil.3.epil, %for.body8.epil.3.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.3.epil

for.cond5.for.cond.cleanup7_crit_edge.3.epil:     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.epil.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil
  %add.lcssa.3.epil = phi float [ %add.lcssa.ph.3.epil, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.epil ], [ %add.epil.3.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.3.epil.loopexit ]
  store float %add.lcssa.3.epil, float* %arrayidx18.3.epil, align 4, !tbaa !3
  %indvars.iv.next56.3.epil = add nuw nsw i64 %indvars.iv55.epil99, 4
  %niter72.nsub.3.epil = add i32 %niter72.epil, -4
  %niter72.ncmp.3.epil.not = icmp eq i32 %niter72.nsub.3.epil, 0
  br i1 %niter72.ncmp.3.epil.not, label %for.cond.cleanup3.loopexit.unr-lcssa.epil.loopexit, label %for.cond5.preheader.epil98, !llvm.loop !11

for.cond.cleanup3.loopexit.unr-lcssa.epil.loopexit: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.epil
  %indvars.iv.next56.3.epil.lcssa = phi i64 [ %indvars.iv.next56.3.epil, %for.cond5.for.cond.cleanup7_crit_edge.3.epil ]
  br label %for.cond.cleanup3.loopexit.unr-lcssa.epil

for.cond.cleanup3.loopexit.unr-lcssa.epil:        ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.epil.loopexit, %for.cond1.preheader.epil
  %indvars.iv55.unr.epil = phi i64 [ 0, %for.cond1.preheader.epil ], [ %indvars.iv.next56.3.epil.lcssa, %for.cond.cleanup3.loopexit.unr-lcssa.epil.loopexit ]
  %lcmp.mod70.epil.not = icmp eq i32 %xtraiter58.epil, 0
  br i1 %lcmp.mod70.epil.not, label %for.cond.cleanup3.epil, label %for.cond5.preheader.epil.epil.preheader

for.cond5.preheader.epil.epil.preheader:          ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.epil
  br label %for.cond5.preheader.epil.epil

for.cond5.preheader.epil.epil:                    ; preds = %for.cond5.preheader.epil.epil.preheader, %for.cond5.for.cond.cleanup7_crit_edge.epil.epil
  %indvars.iv55.epil.epil = phi i64 [ %indvars.iv.next56.epil.epil, %for.cond5.for.cond.cleanup7_crit_edge.epil.epil ], [ %indvars.iv55.unr.epil, %for.cond5.preheader.epil.epil.preheader ]
  %epil.iter69.epil = phi i32 [ %epil.iter69.sub.epil, %for.cond5.for.cond.cleanup7_crit_edge.epil.epil ], [ %xtraiter58.epil, %for.cond5.preheader.epil.epil.preheader ]
  %arrayidx18.epil.epil = getelementptr inbounds float, float* %arrayidx16.epil, i64 %indvars.iv55.epil.epil
  %arrayidx18.promoted.epil.epil = load float, float* %arrayidx18.epil.epil, align 4, !tbaa !3
  %xtraiter.epil.epil = and i32 %n, 3
  %71 = icmp ult i32 %1, 3
  br i1 %71, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil, label %for.body8.lr.ph.new.epil.epil

for.body8.lr.ph.new.epil.epil:                    ; preds = %for.cond5.preheader.epil.epil
  %unroll_iter.epil.epil = and i32 %n, -4
  br label %for.body8.epil59.epil

for.body8.epil59.epil:                            ; preds = %for.body8.epil59.epil, %for.body8.lr.ph.new.epil.epil
  %indvars.iv.epil60.epil = phi i64 [ 0, %for.body8.lr.ph.new.epil.epil ], [ %indvars.iv.next.3.epil.epil, %for.body8.epil59.epil ]
  %add53.epil61.epil = phi float [ %arrayidx18.promoted.epil.epil, %for.body8.lr.ph.new.epil.epil ], [ %add.3.epil.epil, %for.body8.epil59.epil ]
  %niter.epil.epil = phi i32 [ %unroll_iter.epil.epil, %for.body8.lr.ph.new.epil.epil ], [ %niter.nsub.3.epil.epil, %for.body8.epil59.epil ]
  %arrayidx10.epil62.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.epil60.epil
  %72 = load float, float* %arrayidx10.epil62.epil, align 4, !tbaa !3
  %73 = mul nuw nsw i64 %indvars.iv.epil60.epil, %0
  %arrayidx12.epil63.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.epil
  %arrayidx14.epil64.epil = getelementptr inbounds float, float* %arrayidx12.epil63.epil, i64 %73
  %74 = load float, float* %arrayidx14.epil64.epil, align 4, !tbaa !3
  %mul.epil65.epil = fmul float %72, %74
  %add.epil66.epil = fadd float %add53.epil61.epil, %mul.epil65.epil
  %indvars.iv.next.epil67.epil = or i64 %indvars.iv.epil60.epil, 1
  %arrayidx10.1.epil.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.epil67.epil
  %75 = load float, float* %arrayidx10.1.epil.epil, align 4, !tbaa !3
  %76 = mul nuw nsw i64 %indvars.iv.next.epil67.epil, %0
  %arrayidx12.1.epil.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.epil
  %arrayidx14.1.epil.epil = getelementptr inbounds float, float* %arrayidx12.1.epil.epil, i64 %76
  %77 = load float, float* %arrayidx14.1.epil.epil, align 4, !tbaa !3
  %mul.1.epil.epil = fmul float %75, %77
  %add.1.epil.epil = fadd float %add.epil66.epil, %mul.1.epil.epil
  %indvars.iv.next.1.epil.epil = or i64 %indvars.iv.epil60.epil, 2
  %arrayidx10.2.epil.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.1.epil.epil
  %78 = load float, float* %arrayidx10.2.epil.epil, align 4, !tbaa !3
  %79 = mul nuw nsw i64 %indvars.iv.next.1.epil.epil, %0
  %arrayidx12.2.epil.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.epil
  %arrayidx14.2.epil.epil = getelementptr inbounds float, float* %arrayidx12.2.epil.epil, i64 %79
  %80 = load float, float* %arrayidx14.2.epil.epil, align 4, !tbaa !3
  %mul.2.epil.epil = fmul float %78, %80
  %add.2.epil.epil = fadd float %add.1.epil.epil, %mul.2.epil.epil
  %indvars.iv.next.2.epil.epil = or i64 %indvars.iv.epil60.epil, 3
  %arrayidx10.3.epil.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.next.2.epil.epil
  %81 = load float, float* %arrayidx10.3.epil.epil, align 4, !tbaa !3
  %82 = mul nuw nsw i64 %indvars.iv.next.2.epil.epil, %0
  %arrayidx12.3.epil.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.epil
  %arrayidx14.3.epil.epil = getelementptr inbounds float, float* %arrayidx12.3.epil.epil, i64 %82
  %83 = load float, float* %arrayidx14.3.epil.epil, align 4, !tbaa !3
  %mul.3.epil.epil = fmul float %81, %83
  %add.3.epil.epil = fadd float %add.2.epil.epil, %mul.3.epil.epil
  %indvars.iv.next.3.epil.epil = add nuw nsw i64 %indvars.iv.epil60.epil, 4
  %niter.nsub.3.epil.epil = add i32 %niter.epil.epil, -4
  %niter.ncmp.3.epil.epil.not = icmp eq i32 %niter.nsub.3.epil.epil, 0
  br i1 %niter.ncmp.3.epil.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil.loopexit, label %for.body8.epil59.epil, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil.loopexit: ; preds = %for.body8.epil59.epil
  %add.3.epil.epil.lcssa = phi float [ %add.3.epil.epil, %for.body8.epil59.epil ]
  %indvars.iv.next.3.epil.epil.lcssa = phi i64 [ %indvars.iv.next.3.epil.epil, %for.body8.epil59.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil.loopexit, %for.cond5.preheader.epil.epil
  %add.lcssa.ph.epil.epil = phi float [ undef, %for.cond5.preheader.epil.epil ], [ %add.3.epil.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil.loopexit ]
  %indvars.iv.unr.epil.epil = phi i64 [ 0, %for.cond5.preheader.epil.epil ], [ %indvars.iv.next.3.epil.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil.loopexit ]
  %add53.unr.epil.epil = phi float [ %arrayidx18.promoted.epil.epil, %for.cond5.preheader.epil.epil ], [ %add.3.epil.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil.loopexit ]
  %lcmp.mod.epil.epil.not = icmp eq i32 %xtraiter.epil.epil, 0
  br i1 %lcmp.mod.epil.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.epil, label %for.body8.epil.epil.epil.preheader

for.body8.epil.epil.epil.preheader:               ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil
  br label %for.body8.epil.epil.epil

for.body8.epil.epil.epil:                         ; preds = %for.body8.epil.epil.epil.preheader, %for.body8.epil.epil.epil
  %indvars.iv.epil.epil.epil = phi i64 [ %indvars.iv.next.epil.epil.epil, %for.body8.epil.epil.epil ], [ %indvars.iv.unr.epil.epil, %for.body8.epil.epil.epil.preheader ]
  %add53.epil.epil.epil = phi float [ %add.epil.epil.epil, %for.body8.epil.epil.epil ], [ %add53.unr.epil.epil, %for.body8.epil.epil.epil.preheader ]
  %epil.iter.epil.epil = phi i32 [ %epil.iter.sub.epil.epil, %for.body8.epil.epil.epil ], [ %xtraiter.epil.epil, %for.body8.epil.epil.epil.preheader ]
  %arrayidx10.epil.epil.epil = getelementptr inbounds float, float* %arrayidx.epil, i64 %indvars.iv.epil.epil.epil
  %84 = load float, float* %arrayidx10.epil.epil.epil, align 4, !tbaa !3
  %85 = mul nuw nsw i64 %indvars.iv.epil.epil.epil, %0
  %arrayidx12.epil.epil.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.epil
  %arrayidx14.epil.epil.epil = getelementptr inbounds float, float* %arrayidx12.epil.epil.epil, i64 %85
  %86 = load float, float* %arrayidx14.epil.epil.epil, align 4, !tbaa !3
  %mul.epil.epil.epil = fmul float %84, %86
  %add.epil.epil.epil = fadd float %add53.epil.epil.epil, %mul.epil.epil.epil
  %indvars.iv.next.epil.epil.epil = add nuw nsw i64 %indvars.iv.epil.epil.epil, 1
  %epil.iter.sub.epil.epil = add i32 %epil.iter.epil.epil, -1
  %epil.iter.cmp.epil.epil.not = icmp eq i32 %epil.iter.sub.epil.epil, 0
  br i1 %epil.iter.cmp.epil.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.epil.loopexit, label %for.body8.epil.epil.epil, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.epil.epil.loopexit: ; preds = %for.body8.epil.epil.epil
  %add.epil.epil.epil.lcssa = phi float [ %add.epil.epil.epil, %for.body8.epil.epil.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.epil.epil

for.cond5.for.cond.cleanup7_crit_edge.epil.epil:  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil.epil.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil
  %add.lcssa.epil.epil = phi float [ %add.lcssa.ph.epil.epil, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.epil ], [ %add.epil.epil.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.epil.epil.loopexit ]
  store float %add.lcssa.epil.epil, float* %arrayidx18.epil.epil, align 4, !tbaa !3
  %indvars.iv.next56.epil.epil = add nuw nsw i64 %indvars.iv55.epil.epil, 1
  %epil.iter69.sub.epil = add i32 %epil.iter69.epil, -1
  %epil.iter69.cmp.epil.not = icmp eq i32 %epil.iter69.sub.epil, 0
  br i1 %epil.iter69.cmp.epil.not, label %for.cond.cleanup3.epil.loopexit, label %for.cond5.preheader.epil.epil, !llvm.loop !12

for.cond.cleanup3.epil.loopexit:                  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil.epil
  br label %for.cond.cleanup3.epil

for.cond.cleanup3.epil:                           ; preds = %for.cond.cleanup3.epil.loopexit, %for.cond.cleanup3.loopexit.unr-lcssa.epil
  %indvars.iv.next95.epil = add nuw nsw i64 %indvars.iv94.epil, 1
  %epil.iter168.sub = add i32 %epil.iter168, -1
  %epil.iter168.cmp.not = icmp eq i32 %epil.iter168.sub, 0
  br i1 %epil.iter168.cmp.not, label %for.cond.cleanup.loopexit, label %for.cond1.preheader.epil, !llvm.loop !13

for.cond.cleanup.loopexit:                        ; preds = %for.cond.cleanup3.epil
  br label %for.cond.cleanup

for.cond.cleanup:                                 ; preds = %for.cond.cleanup.loopexit, %for.cond.cleanup.loopexit.unr-lcssa, %entry
  ret void

for.cond5.preheader:                              ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3, %for.cond5.preheader.lr.ph.new
  %indvars.iv55 = phi i64 [ 0, %for.cond5.preheader.lr.ph.new ], [ %indvars.iv.next56.3, %for.cond5.for.cond.cleanup7_crit_edge.3 ]
  %niter72 = phi i32 [ %unroll_iter71, %for.cond5.preheader.lr.ph.new ], [ %niter72.nsub.3, %for.cond5.for.cond.cleanup7_crit_edge.3 ]
  %arrayidx18 = getelementptr inbounds float, float* %arrayidx16, i64 %indvars.iv55
  %arrayidx18.promoted = load float, float* %arrayidx18, align 4, !tbaa !3
  %xtraiter = and i32 %n, 3
  %87 = icmp ult i32 %1, 3
  br i1 %87, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa, label %for.body8.lr.ph.new

for.body8.lr.ph.new:                              ; preds = %for.cond5.preheader
  %unroll_iter = and i32 %n, -4
  br label %for.body8

for.cond.cleanup3.loopexit.unr-lcssa.loopexit:    ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3
  %indvars.iv.next56.3.lcssa = phi i64 [ %indvars.iv.next56.3, %for.cond5.for.cond.cleanup7_crit_edge.3 ]
  br label %for.cond.cleanup3.loopexit.unr-lcssa

for.cond.cleanup3.loopexit.unr-lcssa:             ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.loopexit, %for.cond1.preheader
  %indvars.iv55.unr = phi i64 [ 0, %for.cond1.preheader ], [ %indvars.iv.next56.3.lcssa, %for.cond.cleanup3.loopexit.unr-lcssa.loopexit ]
  %lcmp.mod70.not = icmp eq i32 %xtraiter58, 0
  br i1 %lcmp.mod70.not, label %for.cond5.preheader.lr.ph.1, label %for.cond5.preheader.epil.preheader

for.cond5.preheader.epil.preheader:               ; preds = %for.cond.cleanup3.loopexit.unr-lcssa
  br label %for.cond5.preheader.epil

for.cond5.preheader.epil:                         ; preds = %for.cond5.preheader.epil.preheader, %for.cond5.for.cond.cleanup7_crit_edge.epil
  %indvars.iv55.epil = phi i64 [ %indvars.iv.next56.epil, %for.cond5.for.cond.cleanup7_crit_edge.epil ], [ %indvars.iv55.unr, %for.cond5.preheader.epil.preheader ]
  %epil.iter69 = phi i32 [ %epil.iter69.sub, %for.cond5.for.cond.cleanup7_crit_edge.epil ], [ %xtraiter58, %for.cond5.preheader.epil.preheader ]
  %arrayidx18.epil = getelementptr inbounds float, float* %arrayidx16, i64 %indvars.iv55.epil
  %arrayidx18.promoted.epil = load float, float* %arrayidx18.epil, align 4, !tbaa !3
  %xtraiter.epil = and i32 %n, 3
  %88 = icmp ult i32 %1, 3
  br i1 %88, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil, label %for.body8.lr.ph.new.epil

for.body8.lr.ph.new.epil:                         ; preds = %for.cond5.preheader.epil
  %unroll_iter.epil = and i32 %n, -4
  br label %for.body8.epil59

for.body8.epil59:                                 ; preds = %for.body8.epil59, %for.body8.lr.ph.new.epil
  %indvars.iv.epil60 = phi i64 [ 0, %for.body8.lr.ph.new.epil ], [ %indvars.iv.next.3.epil, %for.body8.epil59 ]
  %add53.epil61 = phi float [ %arrayidx18.promoted.epil, %for.body8.lr.ph.new.epil ], [ %add.3.epil, %for.body8.epil59 ]
  %niter.epil = phi i32 [ %unroll_iter.epil, %for.body8.lr.ph.new.epil ], [ %niter.nsub.3.epil, %for.body8.epil59 ]
  %arrayidx10.epil62 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.epil60
  %89 = load float, float* %arrayidx10.epil62, align 4, !tbaa !3
  %90 = mul nuw nsw i64 %indvars.iv.epil60, %0
  %arrayidx12.epil63 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil
  %arrayidx14.epil64 = getelementptr inbounds float, float* %arrayidx12.epil63, i64 %90
  %91 = load float, float* %arrayidx14.epil64, align 4, !tbaa !3
  %mul.epil65 = fmul float %89, %91
  %add.epil66 = fadd float %add53.epil61, %mul.epil65
  %indvars.iv.next.epil67 = or i64 %indvars.iv.epil60, 1
  %arrayidx10.1.epil = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.epil67
  %92 = load float, float* %arrayidx10.1.epil, align 4, !tbaa !3
  %93 = mul nuw nsw i64 %indvars.iv.next.epil67, %0
  %arrayidx12.1.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil
  %arrayidx14.1.epil = getelementptr inbounds float, float* %arrayidx12.1.epil, i64 %93
  %94 = load float, float* %arrayidx14.1.epil, align 4, !tbaa !3
  %mul.1.epil = fmul float %92, %94
  %add.1.epil = fadd float %add.epil66, %mul.1.epil
  %indvars.iv.next.1.epil = or i64 %indvars.iv.epil60, 2
  %arrayidx10.2.epil = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.1.epil
  %95 = load float, float* %arrayidx10.2.epil, align 4, !tbaa !3
  %96 = mul nuw nsw i64 %indvars.iv.next.1.epil, %0
  %arrayidx12.2.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil
  %arrayidx14.2.epil = getelementptr inbounds float, float* %arrayidx12.2.epil, i64 %96
  %97 = load float, float* %arrayidx14.2.epil, align 4, !tbaa !3
  %mul.2.epil = fmul float %95, %97
  %add.2.epil = fadd float %add.1.epil, %mul.2.epil
  %indvars.iv.next.2.epil = or i64 %indvars.iv.epil60, 3
  %arrayidx10.3.epil = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.2.epil
  %98 = load float, float* %arrayidx10.3.epil, align 4, !tbaa !3
  %99 = mul nuw nsw i64 %indvars.iv.next.2.epil, %0
  %arrayidx12.3.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil
  %arrayidx14.3.epil = getelementptr inbounds float, float* %arrayidx12.3.epil, i64 %99
  %100 = load float, float* %arrayidx14.3.epil, align 4, !tbaa !3
  %mul.3.epil = fmul float %98, %100
  %add.3.epil = fadd float %add.2.epil, %mul.3.epil
  %indvars.iv.next.3.epil = add nuw nsw i64 %indvars.iv.epil60, 4
  %niter.nsub.3.epil = add i32 %niter.epil, -4
  %niter.ncmp.3.epil.not = icmp eq i32 %niter.nsub.3.epil, 0
  br i1 %niter.ncmp.3.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.loopexit, label %for.body8.epil59, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.loopexit: ; preds = %for.body8.epil59
  %add.3.epil.lcssa = phi float [ %add.3.epil, %for.body8.epil59 ]
  %indvars.iv.next.3.epil.lcssa = phi i64 [ %indvars.iv.next.3.epil, %for.body8.epil59 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.loopexit, %for.cond5.preheader.epil
  %add.lcssa.ph.epil = phi float [ undef, %for.cond5.preheader.epil ], [ %add.3.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.loopexit ]
  %indvars.iv.unr.epil = phi i64 [ 0, %for.cond5.preheader.epil ], [ %indvars.iv.next.3.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.loopexit ]
  %add53.unr.epil = phi float [ %arrayidx18.promoted.epil, %for.cond5.preheader.epil ], [ %add.3.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.loopexit ]
  %lcmp.mod.epil.not = icmp eq i32 %xtraiter.epil, 0
  br i1 %lcmp.mod.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil, label %for.body8.epil.epil.preheader

for.body8.epil.epil.preheader:                    ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil
  br label %for.body8.epil.epil

for.body8.epil.epil:                              ; preds = %for.body8.epil.epil.preheader, %for.body8.epil.epil
  %indvars.iv.epil.epil = phi i64 [ %indvars.iv.next.epil.epil, %for.body8.epil.epil ], [ %indvars.iv.unr.epil, %for.body8.epil.epil.preheader ]
  %add53.epil.epil = phi float [ %add.epil.epil, %for.body8.epil.epil ], [ %add53.unr.epil, %for.body8.epil.epil.preheader ]
  %epil.iter.epil = phi i32 [ %epil.iter.sub.epil, %for.body8.epil.epil ], [ %xtraiter.epil, %for.body8.epil.epil.preheader ]
  %arrayidx10.epil.epil = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.epil.epil
  %101 = load float, float* %arrayidx10.epil.epil, align 4, !tbaa !3
  %102 = mul nuw nsw i64 %indvars.iv.epil.epil, %0
  %arrayidx12.epil.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil
  %arrayidx14.epil.epil = getelementptr inbounds float, float* %arrayidx12.epil.epil, i64 %102
  %103 = load float, float* %arrayidx14.epil.epil, align 4, !tbaa !3
  %mul.epil.epil = fmul float %101, %103
  %add.epil.epil = fadd float %add53.epil.epil, %mul.epil.epil
  %indvars.iv.next.epil.epil = add nuw nsw i64 %indvars.iv.epil.epil, 1
  %epil.iter.sub.epil = add i32 %epil.iter.epil, -1
  %epil.iter.cmp.epil.not = icmp eq i32 %epil.iter.sub.epil, 0
  br i1 %epil.iter.cmp.epil.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.loopexit, label %for.body8.epil.epil, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.epil.loopexit: ; preds = %for.body8.epil.epil
  %add.epil.epil.lcssa = phi float [ %add.epil.epil, %for.body8.epil.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.epil

for.cond5.for.cond.cleanup7_crit_edge.epil:       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil
  %add.lcssa.epil = phi float [ %add.lcssa.ph.epil, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil ], [ %add.epil.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.epil.loopexit ]
  store float %add.lcssa.epil, float* %arrayidx18.epil, align 4, !tbaa !3
  %indvars.iv.next56.epil = add nuw nsw i64 %indvars.iv55.epil, 1
  %epil.iter69.sub = add i32 %epil.iter69, -1
  %epil.iter69.cmp.not = icmp eq i32 %epil.iter69.sub, 0
  br i1 %epil.iter69.cmp.not, label %for.cond5.preheader.lr.ph.1.loopexit, label %for.cond5.preheader.epil, !llvm.loop !12

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.loopexit: ; preds = %for.body8
  %add.3.lcssa = phi float [ %add.3, %for.body8 ]
  %indvars.iv.next.3.lcssa = phi i64 [ %indvars.iv.next.3, %for.body8 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa:  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.loopexit, %for.cond5.preheader
  %add.lcssa.ph = phi float [ undef, %for.cond5.preheader ], [ %add.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.loopexit ]
  %indvars.iv.unr = phi i64 [ 0, %for.cond5.preheader ], [ %indvars.iv.next.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.loopexit ]
  %add53.unr = phi float [ %arrayidx18.promoted, %for.cond5.preheader ], [ %add.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.loopexit ]
  %lcmp.mod.not = icmp eq i32 %xtraiter, 0
  br i1 %lcmp.mod.not, label %for.cond5.for.cond.cleanup7_crit_edge, label %for.body8.epil.preheader

for.body8.epil.preheader:                         ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa
  br label %for.body8.epil

for.body8.epil:                                   ; preds = %for.body8.epil.preheader, %for.body8.epil
  %indvars.iv.epil = phi i64 [ %indvars.iv.next.epil, %for.body8.epil ], [ %indvars.iv.unr, %for.body8.epil.preheader ]
  %add53.epil = phi float [ %add.epil, %for.body8.epil ], [ %add53.unr, %for.body8.epil.preheader ]
  %epil.iter = phi i32 [ %epil.iter.sub, %for.body8.epil ], [ %xtraiter, %for.body8.epil.preheader ]
  %arrayidx10.epil = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.epil
  %104 = load float, float* %arrayidx10.epil, align 4, !tbaa !3
  %105 = mul nuw nsw i64 %indvars.iv.epil, %0
  %arrayidx12.epil = getelementptr inbounds float, float* %b, i64 %indvars.iv55
  %arrayidx14.epil = getelementptr inbounds float, float* %arrayidx12.epil, i64 %105
  %106 = load float, float* %arrayidx14.epil, align 4, !tbaa !3
  %mul.epil = fmul float %104, %106
  %add.epil = fadd float %add53.epil, %mul.epil
  %indvars.iv.next.epil = add nuw nsw i64 %indvars.iv.epil, 1
  %epil.iter.sub = add i32 %epil.iter, -1
  %epil.iter.cmp.not = icmp eq i32 %epil.iter.sub, 0
  br i1 %epil.iter.cmp.not, label %for.cond5.for.cond.cleanup7_crit_edge.loopexit, label %for.body8.epil, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.loopexit:   ; preds = %for.body8.epil
  %add.epil.lcssa = phi float [ %add.epil, %for.body8.epil ]
  br label %for.cond5.for.cond.cleanup7_crit_edge

for.cond5.for.cond.cleanup7_crit_edge:            ; preds = %for.cond5.for.cond.cleanup7_crit_edge.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa
  %add.lcssa = phi float [ %add.lcssa.ph, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa ], [ %add.epil.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.loopexit ]
  store float %add.lcssa, float* %arrayidx18, align 4, !tbaa !3
  %indvars.iv.next56 = or i64 %indvars.iv55, 1
  %arrayidx18.1 = getelementptr inbounds float, float* %arrayidx16, i64 %indvars.iv.next56
  %arrayidx18.promoted.1 = load float, float* %arrayidx18.1, align 4, !tbaa !3
  %xtraiter.1 = and i32 %n, 3
  %107 = icmp ult i32 %1, 3
  br i1 %107, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1, label %for.body8.lr.ph.new.1

for.body8:                                        ; preds = %for.body8, %for.body8.lr.ph.new
  %indvars.iv = phi i64 [ 0, %for.body8.lr.ph.new ], [ %indvars.iv.next.3, %for.body8 ]
  %add53 = phi float [ %arrayidx18.promoted, %for.body8.lr.ph.new ], [ %add.3, %for.body8 ]
  %niter = phi i32 [ %unroll_iter, %for.body8.lr.ph.new ], [ %niter.nsub.3, %for.body8 ]
  %arrayidx10 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv
  %108 = load float, float* %arrayidx10, align 4, !tbaa !3
  %109 = mul nuw nsw i64 %indvars.iv, %0
  %arrayidx12 = getelementptr inbounds float, float* %b, i64 %indvars.iv55
  %arrayidx14 = getelementptr inbounds float, float* %arrayidx12, i64 %109
  %110 = load float, float* %arrayidx14, align 4, !tbaa !3
  %mul = fmul float %108, %110
  %add = fadd float %add53, %mul
  %indvars.iv.next = or i64 %indvars.iv, 1
  %arrayidx10.1 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next
  %111 = load float, float* %arrayidx10.1, align 4, !tbaa !3
  %112 = mul nuw nsw i64 %indvars.iv.next, %0
  %arrayidx12.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv55
  %arrayidx14.1 = getelementptr inbounds float, float* %arrayidx12.1, i64 %112
  %113 = load float, float* %arrayidx14.1, align 4, !tbaa !3
  %mul.1 = fmul float %111, %113
  %add.1 = fadd float %add, %mul.1
  %indvars.iv.next.1 = or i64 %indvars.iv, 2
  %arrayidx10.2 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.1
  %114 = load float, float* %arrayidx10.2, align 4, !tbaa !3
  %115 = mul nuw nsw i64 %indvars.iv.next.1, %0
  %arrayidx12.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv55
  %arrayidx14.2 = getelementptr inbounds float, float* %arrayidx12.2, i64 %115
  %116 = load float, float* %arrayidx14.2, align 4, !tbaa !3
  %mul.2 = fmul float %114, %116
  %add.2 = fadd float %add.1, %mul.2
  %indvars.iv.next.2 = or i64 %indvars.iv, 3
  %arrayidx10.3 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.2
  %117 = load float, float* %arrayidx10.3, align 4, !tbaa !3
  %118 = mul nuw nsw i64 %indvars.iv.next.2, %0
  %arrayidx12.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv55
  %arrayidx14.3 = getelementptr inbounds float, float* %arrayidx12.3, i64 %118
  %119 = load float, float* %arrayidx14.3, align 4, !tbaa !3
  %mul.3 = fmul float %117, %119
  %add.3 = fadd float %add.2, %mul.3
  %indvars.iv.next.3 = add nuw nsw i64 %indvars.iv, 4
  %niter.nsub.3 = add i32 %niter, -4
  %niter.ncmp.3.not = icmp eq i32 %niter.nsub.3, 0
  br i1 %niter.ncmp.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.loopexit, label %for.body8, !llvm.loop !7

for.body8.lr.ph.new.1:                            ; preds = %for.cond5.for.cond.cleanup7_crit_edge
  %unroll_iter.1 = and i32 %n, -4
  br label %for.body8.1

for.body8.1:                                      ; preds = %for.body8.1, %for.body8.lr.ph.new.1
  %indvars.iv.1 = phi i64 [ 0, %for.body8.lr.ph.new.1 ], [ %indvars.iv.next.3.1, %for.body8.1 ]
  %add53.1 = phi float [ %arrayidx18.promoted.1, %for.body8.lr.ph.new.1 ], [ %add.3.1, %for.body8.1 ]
  %niter.1 = phi i32 [ %unroll_iter.1, %for.body8.lr.ph.new.1 ], [ %niter.nsub.3.1, %for.body8.1 ]
  %arrayidx10.173 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.1
  %120 = load float, float* %arrayidx10.173, align 4, !tbaa !3
  %121 = mul nuw nsw i64 %indvars.iv.1, %0
  %arrayidx12.174 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56
  %arrayidx14.175 = getelementptr inbounds float, float* %arrayidx12.174, i64 %121
  %122 = load float, float* %arrayidx14.175, align 4, !tbaa !3
  %mul.176 = fmul float %120, %122
  %add.177 = fadd float %add53.1, %mul.176
  %indvars.iv.next.178 = or i64 %indvars.iv.1, 1
  %arrayidx10.1.1 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.178
  %123 = load float, float* %arrayidx10.1.1, align 4, !tbaa !3
  %124 = mul nuw nsw i64 %indvars.iv.next.178, %0
  %arrayidx12.1.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56
  %arrayidx14.1.1 = getelementptr inbounds float, float* %arrayidx12.1.1, i64 %124
  %125 = load float, float* %arrayidx14.1.1, align 4, !tbaa !3
  %mul.1.1 = fmul float %123, %125
  %add.1.1 = fadd float %add.177, %mul.1.1
  %indvars.iv.next.1.1 = or i64 %indvars.iv.1, 2
  %arrayidx10.2.1 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.1.1
  %126 = load float, float* %arrayidx10.2.1, align 4, !tbaa !3
  %127 = mul nuw nsw i64 %indvars.iv.next.1.1, %0
  %arrayidx12.2.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56
  %arrayidx14.2.1 = getelementptr inbounds float, float* %arrayidx12.2.1, i64 %127
  %128 = load float, float* %arrayidx14.2.1, align 4, !tbaa !3
  %mul.2.1 = fmul float %126, %128
  %add.2.1 = fadd float %add.1.1, %mul.2.1
  %indvars.iv.next.2.1 = or i64 %indvars.iv.1, 3
  %arrayidx10.3.1 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.2.1
  %129 = load float, float* %arrayidx10.3.1, align 4, !tbaa !3
  %130 = mul nuw nsw i64 %indvars.iv.next.2.1, %0
  %arrayidx12.3.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56
  %arrayidx14.3.1 = getelementptr inbounds float, float* %arrayidx12.3.1, i64 %130
  %131 = load float, float* %arrayidx14.3.1, align 4, !tbaa !3
  %mul.3.1 = fmul float %129, %131
  %add.3.1 = fadd float %add.2.1, %mul.3.1
  %indvars.iv.next.3.1 = add nuw nsw i64 %indvars.iv.1, 4
  %niter.nsub.3.1 = add i32 %niter.1, -4
  %niter.ncmp.3.1.not = icmp eq i32 %niter.nsub.3.1, 0
  br i1 %niter.ncmp.3.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.loopexit, label %for.body8.1, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.loopexit: ; preds = %for.body8.1
  %add.3.1.lcssa = phi float [ %add.3.1, %for.body8.1 ]
  %indvars.iv.next.3.1.lcssa = phi i64 [ %indvars.iv.next.3.1, %for.body8.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.loopexit, %for.cond5.for.cond.cleanup7_crit_edge
  %add.lcssa.ph.1 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge ], [ %add.3.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.loopexit ]
  %indvars.iv.unr.1 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge ], [ %indvars.iv.next.3.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.loopexit ]
  %add53.unr.1 = phi float [ %arrayidx18.promoted.1, %for.cond5.for.cond.cleanup7_crit_edge ], [ %add.3.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.loopexit ]
  %lcmp.mod.1.not = icmp eq i32 %xtraiter.1, 0
  br i1 %lcmp.mod.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.1, label %for.body8.epil.1.preheader

for.body8.epil.1.preheader:                       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1
  br label %for.body8.epil.1

for.body8.epil.1:                                 ; preds = %for.body8.epil.1.preheader, %for.body8.epil.1
  %indvars.iv.epil.1 = phi i64 [ %indvars.iv.next.epil.1, %for.body8.epil.1 ], [ %indvars.iv.unr.1, %for.body8.epil.1.preheader ]
  %add53.epil.1 = phi float [ %add.epil.1, %for.body8.epil.1 ], [ %add53.unr.1, %for.body8.epil.1.preheader ]
  %epil.iter.1 = phi i32 [ %epil.iter.sub.1, %for.body8.epil.1 ], [ %xtraiter.1, %for.body8.epil.1.preheader ]
  %arrayidx10.epil.1 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.epil.1
  %132 = load float, float* %arrayidx10.epil.1, align 4, !tbaa !3
  %133 = mul nuw nsw i64 %indvars.iv.epil.1, %0
  %arrayidx12.epil.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56
  %arrayidx14.epil.1 = getelementptr inbounds float, float* %arrayidx12.epil.1, i64 %133
  %134 = load float, float* %arrayidx14.epil.1, align 4, !tbaa !3
  %mul.epil.1 = fmul float %132, %134
  %add.epil.1 = fadd float %add53.epil.1, %mul.epil.1
  %indvars.iv.next.epil.1 = add nuw nsw i64 %indvars.iv.epil.1, 1
  %epil.iter.sub.1 = add i32 %epil.iter.1, -1
  %epil.iter.cmp.1.not = icmp eq i32 %epil.iter.sub.1, 0
  br i1 %epil.iter.cmp.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.loopexit, label %for.body8.epil.1, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.1.loopexit: ; preds = %for.body8.epil.1
  %add.epil.1.lcssa = phi float [ %add.epil.1, %for.body8.epil.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.1

for.cond5.for.cond.cleanup7_crit_edge.1:          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1
  %add.lcssa.1 = phi float [ %add.lcssa.ph.1, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1 ], [ %add.epil.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.1.loopexit ]
  store float %add.lcssa.1, float* %arrayidx18.1, align 4, !tbaa !3
  %indvars.iv.next56.1 = or i64 %indvars.iv55, 2
  %arrayidx18.2 = getelementptr inbounds float, float* %arrayidx16, i64 %indvars.iv.next56.1
  %arrayidx18.promoted.2 = load float, float* %arrayidx18.2, align 4, !tbaa !3
  %xtraiter.2 = and i32 %n, 3
  %135 = icmp ult i32 %1, 3
  br i1 %135, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2, label %for.body8.lr.ph.new.2

for.body8.lr.ph.new.2:                            ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1
  %unroll_iter.2 = and i32 %n, -4
  br label %for.body8.2

for.body8.2:                                      ; preds = %for.body8.2, %for.body8.lr.ph.new.2
  %indvars.iv.2 = phi i64 [ 0, %for.body8.lr.ph.new.2 ], [ %indvars.iv.next.3.2, %for.body8.2 ]
  %add53.2 = phi float [ %arrayidx18.promoted.2, %for.body8.lr.ph.new.2 ], [ %add.3.2, %for.body8.2 ]
  %niter.2 = phi i32 [ %unroll_iter.2, %for.body8.lr.ph.new.2 ], [ %niter.nsub.3.2, %for.body8.2 ]
  %arrayidx10.280 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.2
  %136 = load float, float* %arrayidx10.280, align 4, !tbaa !3
  %137 = mul nuw nsw i64 %indvars.iv.2, %0
  %arrayidx12.281 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1
  %arrayidx14.282 = getelementptr inbounds float, float* %arrayidx12.281, i64 %137
  %138 = load float, float* %arrayidx14.282, align 4, !tbaa !3
  %mul.283 = fmul float %136, %138
  %add.284 = fadd float %add53.2, %mul.283
  %indvars.iv.next.285 = or i64 %indvars.iv.2, 1
  %arrayidx10.1.2 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.285
  %139 = load float, float* %arrayidx10.1.2, align 4, !tbaa !3
  %140 = mul nuw nsw i64 %indvars.iv.next.285, %0
  %arrayidx12.1.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1
  %arrayidx14.1.2 = getelementptr inbounds float, float* %arrayidx12.1.2, i64 %140
  %141 = load float, float* %arrayidx14.1.2, align 4, !tbaa !3
  %mul.1.2 = fmul float %139, %141
  %add.1.2 = fadd float %add.284, %mul.1.2
  %indvars.iv.next.1.2 = or i64 %indvars.iv.2, 2
  %arrayidx10.2.2 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.1.2
  %142 = load float, float* %arrayidx10.2.2, align 4, !tbaa !3
  %143 = mul nuw nsw i64 %indvars.iv.next.1.2, %0
  %arrayidx12.2.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1
  %arrayidx14.2.2 = getelementptr inbounds float, float* %arrayidx12.2.2, i64 %143
  %144 = load float, float* %arrayidx14.2.2, align 4, !tbaa !3
  %mul.2.2 = fmul float %142, %144
  %add.2.2 = fadd float %add.1.2, %mul.2.2
  %indvars.iv.next.2.2 = or i64 %indvars.iv.2, 3
  %arrayidx10.3.2 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.2.2
  %145 = load float, float* %arrayidx10.3.2, align 4, !tbaa !3
  %146 = mul nuw nsw i64 %indvars.iv.next.2.2, %0
  %arrayidx12.3.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1
  %arrayidx14.3.2 = getelementptr inbounds float, float* %arrayidx12.3.2, i64 %146
  %147 = load float, float* %arrayidx14.3.2, align 4, !tbaa !3
  %mul.3.2 = fmul float %145, %147
  %add.3.2 = fadd float %add.2.2, %mul.3.2
  %indvars.iv.next.3.2 = add nuw nsw i64 %indvars.iv.2, 4
  %niter.nsub.3.2 = add i32 %niter.2, -4
  %niter.ncmp.3.2.not = icmp eq i32 %niter.nsub.3.2, 0
  br i1 %niter.ncmp.3.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.loopexit, label %for.body8.2, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.loopexit: ; preds = %for.body8.2
  %add.3.2.lcssa = phi float [ %add.3.2, %for.body8.2 ]
  %indvars.iv.next.3.2.lcssa = phi i64 [ %indvars.iv.next.3.2, %for.body8.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.1
  %add.lcssa.ph.2 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.1 ], [ %add.3.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.loopexit ]
  %indvars.iv.unr.2 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.1 ], [ %indvars.iv.next.3.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.loopexit ]
  %add53.unr.2 = phi float [ %arrayidx18.promoted.2, %for.cond5.for.cond.cleanup7_crit_edge.1 ], [ %add.3.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.loopexit ]
  %lcmp.mod.2.not = icmp eq i32 %xtraiter.2, 0
  br i1 %lcmp.mod.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.2, label %for.body8.epil.2.preheader

for.body8.epil.2.preheader:                       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2
  br label %for.body8.epil.2

for.body8.epil.2:                                 ; preds = %for.body8.epil.2.preheader, %for.body8.epil.2
  %indvars.iv.epil.2 = phi i64 [ %indvars.iv.next.epil.2, %for.body8.epil.2 ], [ %indvars.iv.unr.2, %for.body8.epil.2.preheader ]
  %add53.epil.2 = phi float [ %add.epil.2, %for.body8.epil.2 ], [ %add53.unr.2, %for.body8.epil.2.preheader ]
  %epil.iter.2 = phi i32 [ %epil.iter.sub.2, %for.body8.epil.2 ], [ %xtraiter.2, %for.body8.epil.2.preheader ]
  %arrayidx10.epil.2 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.epil.2
  %148 = load float, float* %arrayidx10.epil.2, align 4, !tbaa !3
  %149 = mul nuw nsw i64 %indvars.iv.epil.2, %0
  %arrayidx12.epil.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1
  %arrayidx14.epil.2 = getelementptr inbounds float, float* %arrayidx12.epil.2, i64 %149
  %150 = load float, float* %arrayidx14.epil.2, align 4, !tbaa !3
  %mul.epil.2 = fmul float %148, %150
  %add.epil.2 = fadd float %add53.epil.2, %mul.epil.2
  %indvars.iv.next.epil.2 = add nuw nsw i64 %indvars.iv.epil.2, 1
  %epil.iter.sub.2 = add i32 %epil.iter.2, -1
  %epil.iter.cmp.2.not = icmp eq i32 %epil.iter.sub.2, 0
  br i1 %epil.iter.cmp.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.2.loopexit, label %for.body8.epil.2, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.2.loopexit: ; preds = %for.body8.epil.2
  %add.epil.2.lcssa = phi float [ %add.epil.2, %for.body8.epil.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.2

for.cond5.for.cond.cleanup7_crit_edge.2:          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2
  %add.lcssa.2 = phi float [ %add.lcssa.ph.2, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2 ], [ %add.epil.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.2.loopexit ]
  store float %add.lcssa.2, float* %arrayidx18.2, align 4, !tbaa !3
  %indvars.iv.next56.2 = or i64 %indvars.iv55, 3
  %arrayidx18.3 = getelementptr inbounds float, float* %arrayidx16, i64 %indvars.iv.next56.2
  %arrayidx18.promoted.3 = load float, float* %arrayidx18.3, align 4, !tbaa !3
  %xtraiter.3 = and i32 %n, 3
  %151 = icmp ult i32 %1, 3
  br i1 %151, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3, label %for.body8.lr.ph.new.3

for.body8.lr.ph.new.3:                            ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2
  %unroll_iter.3 = and i32 %n, -4
  br label %for.body8.3

for.body8.3:                                      ; preds = %for.body8.3, %for.body8.lr.ph.new.3
  %indvars.iv.3 = phi i64 [ 0, %for.body8.lr.ph.new.3 ], [ %indvars.iv.next.3.3, %for.body8.3 ]
  %add53.3 = phi float [ %arrayidx18.promoted.3, %for.body8.lr.ph.new.3 ], [ %add.3.3, %for.body8.3 ]
  %niter.3 = phi i32 [ %unroll_iter.3, %for.body8.lr.ph.new.3 ], [ %niter.nsub.3.3, %for.body8.3 ]
  %arrayidx10.387 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.3
  %152 = load float, float* %arrayidx10.387, align 4, !tbaa !3
  %153 = mul nuw nsw i64 %indvars.iv.3, %0
  %arrayidx12.388 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2
  %arrayidx14.389 = getelementptr inbounds float, float* %arrayidx12.388, i64 %153
  %154 = load float, float* %arrayidx14.389, align 4, !tbaa !3
  %mul.390 = fmul float %152, %154
  %add.391 = fadd float %add53.3, %mul.390
  %indvars.iv.next.392 = or i64 %indvars.iv.3, 1
  %arrayidx10.1.3 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.392
  %155 = load float, float* %arrayidx10.1.3, align 4, !tbaa !3
  %156 = mul nuw nsw i64 %indvars.iv.next.392, %0
  %arrayidx12.1.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2
  %arrayidx14.1.3 = getelementptr inbounds float, float* %arrayidx12.1.3, i64 %156
  %157 = load float, float* %arrayidx14.1.3, align 4, !tbaa !3
  %mul.1.3 = fmul float %155, %157
  %add.1.3 = fadd float %add.391, %mul.1.3
  %indvars.iv.next.1.3 = or i64 %indvars.iv.3, 2
  %arrayidx10.2.3 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.1.3
  %158 = load float, float* %arrayidx10.2.3, align 4, !tbaa !3
  %159 = mul nuw nsw i64 %indvars.iv.next.1.3, %0
  %arrayidx12.2.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2
  %arrayidx14.2.3 = getelementptr inbounds float, float* %arrayidx12.2.3, i64 %159
  %160 = load float, float* %arrayidx14.2.3, align 4, !tbaa !3
  %mul.2.3 = fmul float %158, %160
  %add.2.3 = fadd float %add.1.3, %mul.2.3
  %indvars.iv.next.2.3 = or i64 %indvars.iv.3, 3
  %arrayidx10.3.3 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.next.2.3
  %161 = load float, float* %arrayidx10.3.3, align 4, !tbaa !3
  %162 = mul nuw nsw i64 %indvars.iv.next.2.3, %0
  %arrayidx12.3.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2
  %arrayidx14.3.3 = getelementptr inbounds float, float* %arrayidx12.3.3, i64 %162
  %163 = load float, float* %arrayidx14.3.3, align 4, !tbaa !3
  %mul.3.3 = fmul float %161, %163
  %add.3.3 = fadd float %add.2.3, %mul.3.3
  %indvars.iv.next.3.3 = add nuw nsw i64 %indvars.iv.3, 4
  %niter.nsub.3.3 = add i32 %niter.3, -4
  %niter.ncmp.3.3.not = icmp eq i32 %niter.nsub.3.3, 0
  br i1 %niter.ncmp.3.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.loopexit, label %for.body8.3, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.loopexit: ; preds = %for.body8.3
  %add.3.3.lcssa = phi float [ %add.3.3, %for.body8.3 ]
  %indvars.iv.next.3.3.lcssa = phi i64 [ %indvars.iv.next.3.3, %for.body8.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.2
  %add.lcssa.ph.3 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.2 ], [ %add.3.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.loopexit ]
  %indvars.iv.unr.3 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.2 ], [ %indvars.iv.next.3.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.loopexit ]
  %add53.unr.3 = phi float [ %arrayidx18.promoted.3, %for.cond5.for.cond.cleanup7_crit_edge.2 ], [ %add.3.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.loopexit ]
  %lcmp.mod.3.not = icmp eq i32 %xtraiter.3, 0
  br i1 %lcmp.mod.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.3, label %for.body8.epil.3.preheader

for.body8.epil.3.preheader:                       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3
  br label %for.body8.epil.3

for.body8.epil.3:                                 ; preds = %for.body8.epil.3.preheader, %for.body8.epil.3
  %indvars.iv.epil.3 = phi i64 [ %indvars.iv.next.epil.3, %for.body8.epil.3 ], [ %indvars.iv.unr.3, %for.body8.epil.3.preheader ]
  %add53.epil.3 = phi float [ %add.epil.3, %for.body8.epil.3 ], [ %add53.unr.3, %for.body8.epil.3.preheader ]
  %epil.iter.3 = phi i32 [ %epil.iter.sub.3, %for.body8.epil.3 ], [ %xtraiter.3, %for.body8.epil.3.preheader ]
  %arrayidx10.epil.3 = getelementptr inbounds float, float* %arrayidx, i64 %indvars.iv.epil.3
  %164 = load float, float* %arrayidx10.epil.3, align 4, !tbaa !3
  %165 = mul nuw nsw i64 %indvars.iv.epil.3, %0
  %arrayidx12.epil.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2
  %arrayidx14.epil.3 = getelementptr inbounds float, float* %arrayidx12.epil.3, i64 %165
  %166 = load float, float* %arrayidx14.epil.3, align 4, !tbaa !3
  %mul.epil.3 = fmul float %164, %166
  %add.epil.3 = fadd float %add53.epil.3, %mul.epil.3
  %indvars.iv.next.epil.3 = add nuw nsw i64 %indvars.iv.epil.3, 1
  %epil.iter.sub.3 = add i32 %epil.iter.3, -1
  %epil.iter.cmp.3.not = icmp eq i32 %epil.iter.sub.3, 0
  br i1 %epil.iter.cmp.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.3.loopexit, label %for.body8.epil.3, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.3.loopexit: ; preds = %for.body8.epil.3
  %add.epil.3.lcssa = phi float [ %add.epil.3, %for.body8.epil.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.3

for.cond5.for.cond.cleanup7_crit_edge.3:          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3
  %add.lcssa.3 = phi float [ %add.lcssa.ph.3, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3 ], [ %add.epil.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.3.loopexit ]
  store float %add.lcssa.3, float* %arrayidx18.3, align 4, !tbaa !3
  %indvars.iv.next56.3 = add nuw nsw i64 %indvars.iv55, 4
  %niter72.nsub.3 = add i32 %niter72, -4
  %niter72.ncmp.3.not = icmp eq i32 %niter72.nsub.3, 0
  br i1 %niter72.ncmp.3.not, label %for.cond.cleanup3.loopexit.unr-lcssa.loopexit, label %for.cond5.preheader, !llvm.loop !11

for.cond5.preheader.lr.ph.1.loopexit:             ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil
  br label %for.cond5.preheader.lr.ph.1

for.cond5.preheader.lr.ph.1:                      ; preds = %for.cond5.preheader.lr.ph.1.loopexit, %for.cond.cleanup3.loopexit.unr-lcssa
  %indvars.iv.next95 = or i64 %indvars.iv94, 1
  %167 = mul nuw nsw i64 %indvars.iv.next95, %0
  %arrayidx.1 = getelementptr inbounds float, float* %a, i64 %167
  %arrayidx16.1 = getelementptr inbounds float, float* %c, i64 %167
  %xtraiter58.1 = and i32 %n, 3
  %168 = icmp ult i32 %1, 3
  br i1 %168, label %for.cond.cleanup3.loopexit.unr-lcssa.1, label %for.cond5.preheader.lr.ph.new.1

for.cond5.preheader.lr.ph.new.1:                  ; preds = %for.cond5.preheader.lr.ph.1
  %unroll_iter71.1 = and i32 %n, -4
  br label %for.cond5.preheader.1

for.cond5.preheader.1:                            ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.1, %for.cond5.preheader.lr.ph.new.1
  %indvars.iv55.1 = phi i64 [ 0, %for.cond5.preheader.lr.ph.new.1 ], [ %indvars.iv.next56.3.1, %for.cond5.for.cond.cleanup7_crit_edge.3.1 ]
  %niter72.1 = phi i32 [ %unroll_iter71.1, %for.cond5.preheader.lr.ph.new.1 ], [ %niter72.nsub.3.1, %for.cond5.for.cond.cleanup7_crit_edge.3.1 ]
  %arrayidx18.1172 = getelementptr inbounds float, float* %arrayidx16.1, i64 %indvars.iv55.1
  %arrayidx18.promoted.1173 = load float, float* %arrayidx18.1172, align 4, !tbaa !3
  %xtraiter.1175 = and i32 %n, 3
  %169 = icmp ult i32 %1, 3
  br i1 %169, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220, label %for.body8.lr.ph.new.1178

for.body8.lr.ph.new.1178:                         ; preds = %for.cond5.preheader.1
  %unroll_iter.1177 = and i32 %n, -4
  br label %for.body8.1211

for.body8.1211:                                   ; preds = %for.body8.1211, %for.body8.lr.ph.new.1178
  %indvars.iv.1179 = phi i64 [ 0, %for.body8.lr.ph.new.1178 ], [ %indvars.iv.next.3.1208, %for.body8.1211 ]
  %add53.1180 = phi float [ %arrayidx18.promoted.1173, %for.body8.lr.ph.new.1178 ], [ %add.3.1207, %for.body8.1211 ]
  %niter.1181 = phi i32 [ %unroll_iter.1177, %for.body8.lr.ph.new.1178 ], [ %niter.nsub.3.1209, %for.body8.1211 ]
  %arrayidx10.1182 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.1179
  %170 = load float, float* %arrayidx10.1182, align 4, !tbaa !3
  %171 = mul nuw nsw i64 %indvars.iv.1179, %0
  %arrayidx12.1183 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.1
  %arrayidx14.1184 = getelementptr inbounds float, float* %arrayidx12.1183, i64 %171
  %172 = load float, float* %arrayidx14.1184, align 4, !tbaa !3
  %mul.1185 = fmul float %170, %172
  %add.1186 = fadd float %add53.1180, %mul.1185
  %indvars.iv.next.1187 = or i64 %indvars.iv.1179, 1
  %arrayidx10.1.1189 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.1187
  %173 = load float, float* %arrayidx10.1.1189, align 4, !tbaa !3
  %174 = mul nuw nsw i64 %indvars.iv.next.1187, %0
  %arrayidx12.1.1190 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.1
  %arrayidx14.1.1191 = getelementptr inbounds float, float* %arrayidx12.1.1190, i64 %174
  %175 = load float, float* %arrayidx14.1.1191, align 4, !tbaa !3
  %mul.1.1192 = fmul float %173, %175
  %add.1.1193 = fadd float %add.1186, %mul.1.1192
  %indvars.iv.next.1.1194 = or i64 %indvars.iv.1179, 2
  %arrayidx10.2.1196 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.1.1194
  %176 = load float, float* %arrayidx10.2.1196, align 4, !tbaa !3
  %177 = mul nuw nsw i64 %indvars.iv.next.1.1194, %0
  %arrayidx12.2.1197 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.1
  %arrayidx14.2.1198 = getelementptr inbounds float, float* %arrayidx12.2.1197, i64 %177
  %178 = load float, float* %arrayidx14.2.1198, align 4, !tbaa !3
  %mul.2.1199 = fmul float %176, %178
  %add.2.1200 = fadd float %add.1.1193, %mul.2.1199
  %indvars.iv.next.2.1201 = or i64 %indvars.iv.1179, 3
  %arrayidx10.3.1203 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.2.1201
  %179 = load float, float* %arrayidx10.3.1203, align 4, !tbaa !3
  %180 = mul nuw nsw i64 %indvars.iv.next.2.1201, %0
  %arrayidx12.3.1204 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.1
  %arrayidx14.3.1205 = getelementptr inbounds float, float* %arrayidx12.3.1204, i64 %180
  %181 = load float, float* %arrayidx14.3.1205, align 4, !tbaa !3
  %mul.3.1206 = fmul float %179, %181
  %add.3.1207 = fadd float %add.2.1200, %mul.3.1206
  %indvars.iv.next.3.1208 = add nuw nsw i64 %indvars.iv.1179, 4
  %niter.nsub.3.1209 = add i32 %niter.1181, -4
  %niter.ncmp.3.1210.not = icmp eq i32 %niter.nsub.3.1209, 0
  br i1 %niter.ncmp.3.1210.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220.loopexit, label %for.body8.1211, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220.loopexit: ; preds = %for.body8.1211
  %add.3.1207.lcssa = phi float [ %add.3.1207, %for.body8.1211 ]
  %indvars.iv.next.3.1208.lcssa = phi i64 [ %indvars.iv.next.3.1208, %for.body8.1211 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220.loopexit, %for.cond5.preheader.1
  %add.lcssa.ph.1216 = phi float [ undef, %for.cond5.preheader.1 ], [ %add.3.1207.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220.loopexit ]
  %indvars.iv.unr.1217 = phi i64 [ 0, %for.cond5.preheader.1 ], [ %indvars.iv.next.3.1208.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220.loopexit ]
  %add53.unr.1218 = phi float [ %arrayidx18.promoted.1173, %for.cond5.preheader.1 ], [ %add.3.1207.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220.loopexit ]
  %lcmp.mod.1219.not = icmp eq i32 %xtraiter.1175, 0
  br i1 %lcmp.mod.1219.not, label %for.cond5.for.cond.cleanup7_crit_edge.1237, label %for.body8.epil.1233.preheader

for.body8.epil.1233.preheader:                    ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220
  br label %for.body8.epil.1233

for.body8.epil.1233:                              ; preds = %for.body8.epil.1233.preheader, %for.body8.epil.1233
  %indvars.iv.epil.1222 = phi i64 [ %indvars.iv.next.epil.1230, %for.body8.epil.1233 ], [ %indvars.iv.unr.1217, %for.body8.epil.1233.preheader ]
  %add53.epil.1223 = phi float [ %add.epil.1229, %for.body8.epil.1233 ], [ %add53.unr.1218, %for.body8.epil.1233.preheader ]
  %epil.iter.1224 = phi i32 [ %epil.iter.sub.1231, %for.body8.epil.1233 ], [ %xtraiter.1175, %for.body8.epil.1233.preheader ]
  %arrayidx10.epil.1225 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.epil.1222
  %182 = load float, float* %arrayidx10.epil.1225, align 4, !tbaa !3
  %183 = mul nuw nsw i64 %indvars.iv.epil.1222, %0
  %arrayidx12.epil.1226 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.1
  %arrayidx14.epil.1227 = getelementptr inbounds float, float* %arrayidx12.epil.1226, i64 %183
  %184 = load float, float* %arrayidx14.epil.1227, align 4, !tbaa !3
  %mul.epil.1228 = fmul float %182, %184
  %add.epil.1229 = fadd float %add53.epil.1223, %mul.epil.1228
  %indvars.iv.next.epil.1230 = add nuw nsw i64 %indvars.iv.epil.1222, 1
  %epil.iter.sub.1231 = add i32 %epil.iter.1224, -1
  %epil.iter.cmp.1232.not = icmp eq i32 %epil.iter.sub.1231, 0
  br i1 %epil.iter.cmp.1232.not, label %for.cond5.for.cond.cleanup7_crit_edge.1237.loopexit, label %for.body8.epil.1233, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.1237.loopexit: ; preds = %for.body8.epil.1233
  %add.epil.1229.lcssa = phi float [ %add.epil.1229, %for.body8.epil.1233 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.1237

for.cond5.for.cond.cleanup7_crit_edge.1237:       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1237.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220
  %add.lcssa.1236 = phi float [ %add.lcssa.ph.1216, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1220 ], [ %add.epil.1229.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.1237.loopexit ]
  store float %add.lcssa.1236, float* %arrayidx18.1172, align 4, !tbaa !3
  %indvars.iv.next56.1238 = or i64 %indvars.iv55.1, 1
  %arrayidx18.1.1 = getelementptr inbounds float, float* %arrayidx16.1, i64 %indvars.iv.next56.1238
  %arrayidx18.promoted.1.1 = load float, float* %arrayidx18.1.1, align 4, !tbaa !3
  %xtraiter.1.1 = and i32 %n, 3
  %185 = icmp ult i32 %1, 3
  br i1 %185, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1, label %for.body8.lr.ph.new.1.1

for.body8.lr.ph.new.1.1:                          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1237
  %unroll_iter.1.1 = and i32 %n, -4
  br label %for.body8.1.1

for.body8.1.1:                                    ; preds = %for.body8.1.1, %for.body8.lr.ph.new.1.1
  %indvars.iv.1.1 = phi i64 [ 0, %for.body8.lr.ph.new.1.1 ], [ %indvars.iv.next.3.1.1, %for.body8.1.1 ]
  %add53.1.1 = phi float [ %arrayidx18.promoted.1.1, %for.body8.lr.ph.new.1.1 ], [ %add.3.1.1, %for.body8.1.1 ]
  %niter.1.1 = phi i32 [ %unroll_iter.1.1, %for.body8.lr.ph.new.1.1 ], [ %niter.nsub.3.1.1, %for.body8.1.1 ]
  %arrayidx10.173.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.1.1
  %186 = load float, float* %arrayidx10.173.1, align 4, !tbaa !3
  %187 = mul nuw nsw i64 %indvars.iv.1.1, %0
  %arrayidx12.174.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1238
  %arrayidx14.175.1 = getelementptr inbounds float, float* %arrayidx12.174.1, i64 %187
  %188 = load float, float* %arrayidx14.175.1, align 4, !tbaa !3
  %mul.176.1 = fmul float %186, %188
  %add.177.1 = fadd float %add53.1.1, %mul.176.1
  %indvars.iv.next.178.1 = or i64 %indvars.iv.1.1, 1
  %arrayidx10.1.1.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.178.1
  %189 = load float, float* %arrayidx10.1.1.1, align 4, !tbaa !3
  %190 = mul nuw nsw i64 %indvars.iv.next.178.1, %0
  %arrayidx12.1.1.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1238
  %arrayidx14.1.1.1 = getelementptr inbounds float, float* %arrayidx12.1.1.1, i64 %190
  %191 = load float, float* %arrayidx14.1.1.1, align 4, !tbaa !3
  %mul.1.1.1 = fmul float %189, %191
  %add.1.1.1 = fadd float %add.177.1, %mul.1.1.1
  %indvars.iv.next.1.1.1 = or i64 %indvars.iv.1.1, 2
  %arrayidx10.2.1.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.1.1.1
  %192 = load float, float* %arrayidx10.2.1.1, align 4, !tbaa !3
  %193 = mul nuw nsw i64 %indvars.iv.next.1.1.1, %0
  %arrayidx12.2.1.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1238
  %arrayidx14.2.1.1 = getelementptr inbounds float, float* %arrayidx12.2.1.1, i64 %193
  %194 = load float, float* %arrayidx14.2.1.1, align 4, !tbaa !3
  %mul.2.1.1 = fmul float %192, %194
  %add.2.1.1 = fadd float %add.1.1.1, %mul.2.1.1
  %indvars.iv.next.2.1.1 = or i64 %indvars.iv.1.1, 3
  %arrayidx10.3.1.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.2.1.1
  %195 = load float, float* %arrayidx10.3.1.1, align 4, !tbaa !3
  %196 = mul nuw nsw i64 %indvars.iv.next.2.1.1, %0
  %arrayidx12.3.1.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1238
  %arrayidx14.3.1.1 = getelementptr inbounds float, float* %arrayidx12.3.1.1, i64 %196
  %197 = load float, float* %arrayidx14.3.1.1, align 4, !tbaa !3
  %mul.3.1.1 = fmul float %195, %197
  %add.3.1.1 = fadd float %add.2.1.1, %mul.3.1.1
  %indvars.iv.next.3.1.1 = add nuw nsw i64 %indvars.iv.1.1, 4
  %niter.nsub.3.1.1 = add i32 %niter.1.1, -4
  %niter.ncmp.3.1.1.not = icmp eq i32 %niter.nsub.3.1.1, 0
  br i1 %niter.ncmp.3.1.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1.loopexit, label %for.body8.1.1, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1.loopexit: ; preds = %for.body8.1.1
  %add.3.1.1.lcssa = phi float [ %add.3.1.1, %for.body8.1.1 ]
  %indvars.iv.next.3.1.1.lcssa = phi i64 [ %indvars.iv.next.3.1.1, %for.body8.1.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.1237
  %add.lcssa.ph.1.1 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.1237 ], [ %add.3.1.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1.loopexit ]
  %indvars.iv.unr.1.1 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.1237 ], [ %indvars.iv.next.3.1.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1.loopexit ]
  %add53.unr.1.1 = phi float [ %arrayidx18.promoted.1.1, %for.cond5.for.cond.cleanup7_crit_edge.1237 ], [ %add.3.1.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1.loopexit ]
  %lcmp.mod.1.1.not = icmp eq i32 %xtraiter.1.1, 0
  br i1 %lcmp.mod.1.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.1, label %for.body8.epil.1.1.preheader

for.body8.epil.1.1.preheader:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1
  br label %for.body8.epil.1.1

for.body8.epil.1.1:                               ; preds = %for.body8.epil.1.1.preheader, %for.body8.epil.1.1
  %indvars.iv.epil.1.1 = phi i64 [ %indvars.iv.next.epil.1.1, %for.body8.epil.1.1 ], [ %indvars.iv.unr.1.1, %for.body8.epil.1.1.preheader ]
  %add53.epil.1.1 = phi float [ %add.epil.1.1, %for.body8.epil.1.1 ], [ %add53.unr.1.1, %for.body8.epil.1.1.preheader ]
  %epil.iter.1.1 = phi i32 [ %epil.iter.sub.1.1, %for.body8.epil.1.1 ], [ %xtraiter.1.1, %for.body8.epil.1.1.preheader ]
  %arrayidx10.epil.1.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.epil.1.1
  %198 = load float, float* %arrayidx10.epil.1.1, align 4, !tbaa !3
  %199 = mul nuw nsw i64 %indvars.iv.epil.1.1, %0
  %arrayidx12.epil.1.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1238
  %arrayidx14.epil.1.1 = getelementptr inbounds float, float* %arrayidx12.epil.1.1, i64 %199
  %200 = load float, float* %arrayidx14.epil.1.1, align 4, !tbaa !3
  %mul.epil.1.1 = fmul float %198, %200
  %add.epil.1.1 = fadd float %add53.epil.1.1, %mul.epil.1.1
  %indvars.iv.next.epil.1.1 = add nuw nsw i64 %indvars.iv.epil.1.1, 1
  %epil.iter.sub.1.1 = add i32 %epil.iter.1.1, -1
  %epil.iter.cmp.1.1.not = icmp eq i32 %epil.iter.sub.1.1, 0
  br i1 %epil.iter.cmp.1.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.1.loopexit, label %for.body8.epil.1.1, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.1.1.loopexit: ; preds = %for.body8.epil.1.1
  %add.epil.1.1.lcssa = phi float [ %add.epil.1.1, %for.body8.epil.1.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.1.1

for.cond5.for.cond.cleanup7_crit_edge.1.1:        ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.1.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1
  %add.lcssa.1.1 = phi float [ %add.lcssa.ph.1.1, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.1 ], [ %add.epil.1.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.1.1.loopexit ]
  store float %add.lcssa.1.1, float* %arrayidx18.1.1, align 4, !tbaa !3
  %indvars.iv.next56.1.1 = or i64 %indvars.iv55.1, 2
  %arrayidx18.2.1 = getelementptr inbounds float, float* %arrayidx16.1, i64 %indvars.iv.next56.1.1
  %arrayidx18.promoted.2.1 = load float, float* %arrayidx18.2.1, align 4, !tbaa !3
  %xtraiter.2.1 = and i32 %n, 3
  %201 = icmp ult i32 %1, 3
  br i1 %201, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1, label %for.body8.lr.ph.new.2.1

for.body8.lr.ph.new.2.1:                          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.1
  %unroll_iter.2.1 = and i32 %n, -4
  br label %for.body8.2.1

for.body8.2.1:                                    ; preds = %for.body8.2.1, %for.body8.lr.ph.new.2.1
  %indvars.iv.2.1 = phi i64 [ 0, %for.body8.lr.ph.new.2.1 ], [ %indvars.iv.next.3.2.1, %for.body8.2.1 ]
  %add53.2.1 = phi float [ %arrayidx18.promoted.2.1, %for.body8.lr.ph.new.2.1 ], [ %add.3.2.1, %for.body8.2.1 ]
  %niter.2.1 = phi i32 [ %unroll_iter.2.1, %for.body8.lr.ph.new.2.1 ], [ %niter.nsub.3.2.1, %for.body8.2.1 ]
  %arrayidx10.280.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.2.1
  %202 = load float, float* %arrayidx10.280.1, align 4, !tbaa !3
  %203 = mul nuw nsw i64 %indvars.iv.2.1, %0
  %arrayidx12.281.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.1
  %arrayidx14.282.1 = getelementptr inbounds float, float* %arrayidx12.281.1, i64 %203
  %204 = load float, float* %arrayidx14.282.1, align 4, !tbaa !3
  %mul.283.1 = fmul float %202, %204
  %add.284.1 = fadd float %add53.2.1, %mul.283.1
  %indvars.iv.next.285.1 = or i64 %indvars.iv.2.1, 1
  %arrayidx10.1.2.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.285.1
  %205 = load float, float* %arrayidx10.1.2.1, align 4, !tbaa !3
  %206 = mul nuw nsw i64 %indvars.iv.next.285.1, %0
  %arrayidx12.1.2.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.1
  %arrayidx14.1.2.1 = getelementptr inbounds float, float* %arrayidx12.1.2.1, i64 %206
  %207 = load float, float* %arrayidx14.1.2.1, align 4, !tbaa !3
  %mul.1.2.1 = fmul float %205, %207
  %add.1.2.1 = fadd float %add.284.1, %mul.1.2.1
  %indvars.iv.next.1.2.1 = or i64 %indvars.iv.2.1, 2
  %arrayidx10.2.2.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.1.2.1
  %208 = load float, float* %arrayidx10.2.2.1, align 4, !tbaa !3
  %209 = mul nuw nsw i64 %indvars.iv.next.1.2.1, %0
  %arrayidx12.2.2.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.1
  %arrayidx14.2.2.1 = getelementptr inbounds float, float* %arrayidx12.2.2.1, i64 %209
  %210 = load float, float* %arrayidx14.2.2.1, align 4, !tbaa !3
  %mul.2.2.1 = fmul float %208, %210
  %add.2.2.1 = fadd float %add.1.2.1, %mul.2.2.1
  %indvars.iv.next.2.2.1 = or i64 %indvars.iv.2.1, 3
  %arrayidx10.3.2.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.2.2.1
  %211 = load float, float* %arrayidx10.3.2.1, align 4, !tbaa !3
  %212 = mul nuw nsw i64 %indvars.iv.next.2.2.1, %0
  %arrayidx12.3.2.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.1
  %arrayidx14.3.2.1 = getelementptr inbounds float, float* %arrayidx12.3.2.1, i64 %212
  %213 = load float, float* %arrayidx14.3.2.1, align 4, !tbaa !3
  %mul.3.2.1 = fmul float %211, %213
  %add.3.2.1 = fadd float %add.2.2.1, %mul.3.2.1
  %indvars.iv.next.3.2.1 = add nuw nsw i64 %indvars.iv.2.1, 4
  %niter.nsub.3.2.1 = add i32 %niter.2.1, -4
  %niter.ncmp.3.2.1.not = icmp eq i32 %niter.nsub.3.2.1, 0
  br i1 %niter.ncmp.3.2.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1.loopexit, label %for.body8.2.1, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1.loopexit: ; preds = %for.body8.2.1
  %add.3.2.1.lcssa = phi float [ %add.3.2.1, %for.body8.2.1 ]
  %indvars.iv.next.3.2.1.lcssa = phi i64 [ %indvars.iv.next.3.2.1, %for.body8.2.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.1.1
  %add.lcssa.ph.2.1 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.1.1 ], [ %add.3.2.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1.loopexit ]
  %indvars.iv.unr.2.1 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.1.1 ], [ %indvars.iv.next.3.2.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1.loopexit ]
  %add53.unr.2.1 = phi float [ %arrayidx18.promoted.2.1, %for.cond5.for.cond.cleanup7_crit_edge.1.1 ], [ %add.3.2.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1.loopexit ]
  %lcmp.mod.2.1.not = icmp eq i32 %xtraiter.2.1, 0
  br i1 %lcmp.mod.2.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.2.1, label %for.body8.epil.2.1.preheader

for.body8.epil.2.1.preheader:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1
  br label %for.body8.epil.2.1

for.body8.epil.2.1:                               ; preds = %for.body8.epil.2.1.preheader, %for.body8.epil.2.1
  %indvars.iv.epil.2.1 = phi i64 [ %indvars.iv.next.epil.2.1, %for.body8.epil.2.1 ], [ %indvars.iv.unr.2.1, %for.body8.epil.2.1.preheader ]
  %add53.epil.2.1 = phi float [ %add.epil.2.1, %for.body8.epil.2.1 ], [ %add53.unr.2.1, %for.body8.epil.2.1.preheader ]
  %epil.iter.2.1 = phi i32 [ %epil.iter.sub.2.1, %for.body8.epil.2.1 ], [ %xtraiter.2.1, %for.body8.epil.2.1.preheader ]
  %arrayidx10.epil.2.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.epil.2.1
  %214 = load float, float* %arrayidx10.epil.2.1, align 4, !tbaa !3
  %215 = mul nuw nsw i64 %indvars.iv.epil.2.1, %0
  %arrayidx12.epil.2.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.1
  %arrayidx14.epil.2.1 = getelementptr inbounds float, float* %arrayidx12.epil.2.1, i64 %215
  %216 = load float, float* %arrayidx14.epil.2.1, align 4, !tbaa !3
  %mul.epil.2.1 = fmul float %214, %216
  %add.epil.2.1 = fadd float %add53.epil.2.1, %mul.epil.2.1
  %indvars.iv.next.epil.2.1 = add nuw nsw i64 %indvars.iv.epil.2.1, 1
  %epil.iter.sub.2.1 = add i32 %epil.iter.2.1, -1
  %epil.iter.cmp.2.1.not = icmp eq i32 %epil.iter.sub.2.1, 0
  br i1 %epil.iter.cmp.2.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.2.1.loopexit, label %for.body8.epil.2.1, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.2.1.loopexit: ; preds = %for.body8.epil.2.1
  %add.epil.2.1.lcssa = phi float [ %add.epil.2.1, %for.body8.epil.2.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.2.1

for.cond5.for.cond.cleanup7_crit_edge.2.1:        ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2.1.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1
  %add.lcssa.2.1 = phi float [ %add.lcssa.ph.2.1, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.1 ], [ %add.epil.2.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.2.1.loopexit ]
  store float %add.lcssa.2.1, float* %arrayidx18.2.1, align 4, !tbaa !3
  %indvars.iv.next56.2.1 = or i64 %indvars.iv55.1, 3
  %arrayidx18.3.1 = getelementptr inbounds float, float* %arrayidx16.1, i64 %indvars.iv.next56.2.1
  %arrayidx18.promoted.3.1 = load float, float* %arrayidx18.3.1, align 4, !tbaa !3
  %xtraiter.3.1 = and i32 %n, 3
  %217 = icmp ult i32 %1, 3
  br i1 %217, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1, label %for.body8.lr.ph.new.3.1

for.body8.lr.ph.new.3.1:                          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2.1
  %unroll_iter.3.1 = and i32 %n, -4
  br label %for.body8.3.1

for.body8.3.1:                                    ; preds = %for.body8.3.1, %for.body8.lr.ph.new.3.1
  %indvars.iv.3.1 = phi i64 [ 0, %for.body8.lr.ph.new.3.1 ], [ %indvars.iv.next.3.3.1, %for.body8.3.1 ]
  %add53.3.1 = phi float [ %arrayidx18.promoted.3.1, %for.body8.lr.ph.new.3.1 ], [ %add.3.3.1, %for.body8.3.1 ]
  %niter.3.1 = phi i32 [ %unroll_iter.3.1, %for.body8.lr.ph.new.3.1 ], [ %niter.nsub.3.3.1, %for.body8.3.1 ]
  %arrayidx10.387.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.3.1
  %218 = load float, float* %arrayidx10.387.1, align 4, !tbaa !3
  %219 = mul nuw nsw i64 %indvars.iv.3.1, %0
  %arrayidx12.388.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.1
  %arrayidx14.389.1 = getelementptr inbounds float, float* %arrayidx12.388.1, i64 %219
  %220 = load float, float* %arrayidx14.389.1, align 4, !tbaa !3
  %mul.390.1 = fmul float %218, %220
  %add.391.1 = fadd float %add53.3.1, %mul.390.1
  %indvars.iv.next.392.1 = or i64 %indvars.iv.3.1, 1
  %arrayidx10.1.3.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.392.1
  %221 = load float, float* %arrayidx10.1.3.1, align 4, !tbaa !3
  %222 = mul nuw nsw i64 %indvars.iv.next.392.1, %0
  %arrayidx12.1.3.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.1
  %arrayidx14.1.3.1 = getelementptr inbounds float, float* %arrayidx12.1.3.1, i64 %222
  %223 = load float, float* %arrayidx14.1.3.1, align 4, !tbaa !3
  %mul.1.3.1 = fmul float %221, %223
  %add.1.3.1 = fadd float %add.391.1, %mul.1.3.1
  %indvars.iv.next.1.3.1 = or i64 %indvars.iv.3.1, 2
  %arrayidx10.2.3.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.1.3.1
  %224 = load float, float* %arrayidx10.2.3.1, align 4, !tbaa !3
  %225 = mul nuw nsw i64 %indvars.iv.next.1.3.1, %0
  %arrayidx12.2.3.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.1
  %arrayidx14.2.3.1 = getelementptr inbounds float, float* %arrayidx12.2.3.1, i64 %225
  %226 = load float, float* %arrayidx14.2.3.1, align 4, !tbaa !3
  %mul.2.3.1 = fmul float %224, %226
  %add.2.3.1 = fadd float %add.1.3.1, %mul.2.3.1
  %indvars.iv.next.2.3.1 = or i64 %indvars.iv.3.1, 3
  %arrayidx10.3.3.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.2.3.1
  %227 = load float, float* %arrayidx10.3.3.1, align 4, !tbaa !3
  %228 = mul nuw nsw i64 %indvars.iv.next.2.3.1, %0
  %arrayidx12.3.3.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.1
  %arrayidx14.3.3.1 = getelementptr inbounds float, float* %arrayidx12.3.3.1, i64 %228
  %229 = load float, float* %arrayidx14.3.3.1, align 4, !tbaa !3
  %mul.3.3.1 = fmul float %227, %229
  %add.3.3.1 = fadd float %add.2.3.1, %mul.3.3.1
  %indvars.iv.next.3.3.1 = add nuw nsw i64 %indvars.iv.3.1, 4
  %niter.nsub.3.3.1 = add i32 %niter.3.1, -4
  %niter.ncmp.3.3.1.not = icmp eq i32 %niter.nsub.3.3.1, 0
  br i1 %niter.ncmp.3.3.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1.loopexit, label %for.body8.3.1, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1.loopexit: ; preds = %for.body8.3.1
  %add.3.3.1.lcssa = phi float [ %add.3.3.1, %for.body8.3.1 ]
  %indvars.iv.next.3.3.1.lcssa = phi i64 [ %indvars.iv.next.3.3.1, %for.body8.3.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.2.1
  %add.lcssa.ph.3.1 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.2.1 ], [ %add.3.3.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1.loopexit ]
  %indvars.iv.unr.3.1 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.2.1 ], [ %indvars.iv.next.3.3.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1.loopexit ]
  %add53.unr.3.1 = phi float [ %arrayidx18.promoted.3.1, %for.cond5.for.cond.cleanup7_crit_edge.2.1 ], [ %add.3.3.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1.loopexit ]
  %lcmp.mod.3.1.not = icmp eq i32 %xtraiter.3.1, 0
  br i1 %lcmp.mod.3.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.3.1, label %for.body8.epil.3.1.preheader

for.body8.epil.3.1.preheader:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1
  br label %for.body8.epil.3.1

for.body8.epil.3.1:                               ; preds = %for.body8.epil.3.1.preheader, %for.body8.epil.3.1
  %indvars.iv.epil.3.1 = phi i64 [ %indvars.iv.next.epil.3.1, %for.body8.epil.3.1 ], [ %indvars.iv.unr.3.1, %for.body8.epil.3.1.preheader ]
  %add53.epil.3.1 = phi float [ %add.epil.3.1, %for.body8.epil.3.1 ], [ %add53.unr.3.1, %for.body8.epil.3.1.preheader ]
  %epil.iter.3.1 = phi i32 [ %epil.iter.sub.3.1, %for.body8.epil.3.1 ], [ %xtraiter.3.1, %for.body8.epil.3.1.preheader ]
  %arrayidx10.epil.3.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.epil.3.1
  %230 = load float, float* %arrayidx10.epil.3.1, align 4, !tbaa !3
  %231 = mul nuw nsw i64 %indvars.iv.epil.3.1, %0
  %arrayidx12.epil.3.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.1
  %arrayidx14.epil.3.1 = getelementptr inbounds float, float* %arrayidx12.epil.3.1, i64 %231
  %232 = load float, float* %arrayidx14.epil.3.1, align 4, !tbaa !3
  %mul.epil.3.1 = fmul float %230, %232
  %add.epil.3.1 = fadd float %add53.epil.3.1, %mul.epil.3.1
  %indvars.iv.next.epil.3.1 = add nuw nsw i64 %indvars.iv.epil.3.1, 1
  %epil.iter.sub.3.1 = add i32 %epil.iter.3.1, -1
  %epil.iter.cmp.3.1.not = icmp eq i32 %epil.iter.sub.3.1, 0
  br i1 %epil.iter.cmp.3.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.3.1.loopexit, label %for.body8.epil.3.1, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.3.1.loopexit: ; preds = %for.body8.epil.3.1
  %add.epil.3.1.lcssa = phi float [ %add.epil.3.1, %for.body8.epil.3.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.3.1

for.cond5.for.cond.cleanup7_crit_edge.3.1:        ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.1.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1
  %add.lcssa.3.1 = phi float [ %add.lcssa.ph.3.1, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.1 ], [ %add.epil.3.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.3.1.loopexit ]
  store float %add.lcssa.3.1, float* %arrayidx18.3.1, align 4, !tbaa !3
  %indvars.iv.next56.3.1 = add nuw nsw i64 %indvars.iv55.1, 4
  %niter72.nsub.3.1 = add i32 %niter72.1, -4
  %niter72.ncmp.3.1.not = icmp eq i32 %niter72.nsub.3.1, 0
  br i1 %niter72.ncmp.3.1.not, label %for.cond.cleanup3.loopexit.unr-lcssa.1.loopexit, label %for.cond5.preheader.1, !llvm.loop !11

for.cond.cleanup3.loopexit.unr-lcssa.1.loopexit:  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.1
  %indvars.iv.next56.3.1.lcssa = phi i64 [ %indvars.iv.next56.3.1, %for.cond5.for.cond.cleanup7_crit_edge.3.1 ]
  br label %for.cond.cleanup3.loopexit.unr-lcssa.1

for.cond.cleanup3.loopexit.unr-lcssa.1:           ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.1.loopexit, %for.cond5.preheader.lr.ph.1
  %indvars.iv55.unr.1 = phi i64 [ 0, %for.cond5.preheader.lr.ph.1 ], [ %indvars.iv.next56.3.1.lcssa, %for.cond.cleanup3.loopexit.unr-lcssa.1.loopexit ]
  %lcmp.mod70.1.not = icmp eq i32 %xtraiter58.1, 0
  br i1 %lcmp.mod70.1.not, label %for.cond5.preheader.lr.ph.2, label %for.cond5.preheader.epil.1.preheader

for.cond5.preheader.epil.1.preheader:             ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.1
  br label %for.cond5.preheader.epil.1

for.cond5.preheader.epil.1:                       ; preds = %for.cond5.preheader.epil.1.preheader, %for.cond5.for.cond.cleanup7_crit_edge.epil.1
  %indvars.iv55.epil.1 = phi i64 [ %indvars.iv.next56.epil.1, %for.cond5.for.cond.cleanup7_crit_edge.epil.1 ], [ %indvars.iv55.unr.1, %for.cond5.preheader.epil.1.preheader ]
  %epil.iter69.1 = phi i32 [ %epil.iter69.sub.1, %for.cond5.for.cond.cleanup7_crit_edge.epil.1 ], [ %xtraiter58.1, %for.cond5.preheader.epil.1.preheader ]
  %arrayidx18.epil.1 = getelementptr inbounds float, float* %arrayidx16.1, i64 %indvars.iv55.epil.1
  %arrayidx18.promoted.epil.1 = load float, float* %arrayidx18.epil.1, align 4, !tbaa !3
  %xtraiter.epil.1 = and i32 %n, 3
  %233 = icmp ult i32 %1, 3
  br i1 %233, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1, label %for.body8.lr.ph.new.epil.1

for.body8.lr.ph.new.epil.1:                       ; preds = %for.cond5.preheader.epil.1
  %unroll_iter.epil.1 = and i32 %n, -4
  br label %for.body8.epil59.1

for.body8.epil59.1:                               ; preds = %for.body8.epil59.1, %for.body8.lr.ph.new.epil.1
  %indvars.iv.epil60.1 = phi i64 [ 0, %for.body8.lr.ph.new.epil.1 ], [ %indvars.iv.next.3.epil.1, %for.body8.epil59.1 ]
  %add53.epil61.1 = phi float [ %arrayidx18.promoted.epil.1, %for.body8.lr.ph.new.epil.1 ], [ %add.3.epil.1, %for.body8.epil59.1 ]
  %niter.epil.1 = phi i32 [ %unroll_iter.epil.1, %for.body8.lr.ph.new.epil.1 ], [ %niter.nsub.3.epil.1, %for.body8.epil59.1 ]
  %arrayidx10.epil62.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.epil60.1
  %234 = load float, float* %arrayidx10.epil62.1, align 4, !tbaa !3
  %235 = mul nuw nsw i64 %indvars.iv.epil60.1, %0
  %arrayidx12.epil63.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.1
  %arrayidx14.epil64.1 = getelementptr inbounds float, float* %arrayidx12.epil63.1, i64 %235
  %236 = load float, float* %arrayidx14.epil64.1, align 4, !tbaa !3
  %mul.epil65.1 = fmul float %234, %236
  %add.epil66.1 = fadd float %add53.epil61.1, %mul.epil65.1
  %indvars.iv.next.epil67.1 = or i64 %indvars.iv.epil60.1, 1
  %arrayidx10.1.epil.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.epil67.1
  %237 = load float, float* %arrayidx10.1.epil.1, align 4, !tbaa !3
  %238 = mul nuw nsw i64 %indvars.iv.next.epil67.1, %0
  %arrayidx12.1.epil.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.1
  %arrayidx14.1.epil.1 = getelementptr inbounds float, float* %arrayidx12.1.epil.1, i64 %238
  %239 = load float, float* %arrayidx14.1.epil.1, align 4, !tbaa !3
  %mul.1.epil.1 = fmul float %237, %239
  %add.1.epil.1 = fadd float %add.epil66.1, %mul.1.epil.1
  %indvars.iv.next.1.epil.1 = or i64 %indvars.iv.epil60.1, 2
  %arrayidx10.2.epil.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.1.epil.1
  %240 = load float, float* %arrayidx10.2.epil.1, align 4, !tbaa !3
  %241 = mul nuw nsw i64 %indvars.iv.next.1.epil.1, %0
  %arrayidx12.2.epil.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.1
  %arrayidx14.2.epil.1 = getelementptr inbounds float, float* %arrayidx12.2.epil.1, i64 %241
  %242 = load float, float* %arrayidx14.2.epil.1, align 4, !tbaa !3
  %mul.2.epil.1 = fmul float %240, %242
  %add.2.epil.1 = fadd float %add.1.epil.1, %mul.2.epil.1
  %indvars.iv.next.2.epil.1 = or i64 %indvars.iv.epil60.1, 3
  %arrayidx10.3.epil.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.next.2.epil.1
  %243 = load float, float* %arrayidx10.3.epil.1, align 4, !tbaa !3
  %244 = mul nuw nsw i64 %indvars.iv.next.2.epil.1, %0
  %arrayidx12.3.epil.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.1
  %arrayidx14.3.epil.1 = getelementptr inbounds float, float* %arrayidx12.3.epil.1, i64 %244
  %245 = load float, float* %arrayidx14.3.epil.1, align 4, !tbaa !3
  %mul.3.epil.1 = fmul float %243, %245
  %add.3.epil.1 = fadd float %add.2.epil.1, %mul.3.epil.1
  %indvars.iv.next.3.epil.1 = add nuw nsw i64 %indvars.iv.epil60.1, 4
  %niter.nsub.3.epil.1 = add i32 %niter.epil.1, -4
  %niter.ncmp.3.epil.1.not = icmp eq i32 %niter.nsub.3.epil.1, 0
  br i1 %niter.ncmp.3.epil.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1.loopexit, label %for.body8.epil59.1, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1.loopexit: ; preds = %for.body8.epil59.1
  %add.3.epil.1.lcssa = phi float [ %add.3.epil.1, %for.body8.epil59.1 ]
  %indvars.iv.next.3.epil.1.lcssa = phi i64 [ %indvars.iv.next.3.epil.1, %for.body8.epil59.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1.loopexit, %for.cond5.preheader.epil.1
  %add.lcssa.ph.epil.1 = phi float [ undef, %for.cond5.preheader.epil.1 ], [ %add.3.epil.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1.loopexit ]
  %indvars.iv.unr.epil.1 = phi i64 [ 0, %for.cond5.preheader.epil.1 ], [ %indvars.iv.next.3.epil.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1.loopexit ]
  %add53.unr.epil.1 = phi float [ %arrayidx18.promoted.epil.1, %for.cond5.preheader.epil.1 ], [ %add.3.epil.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1.loopexit ]
  %lcmp.mod.epil.1.not = icmp eq i32 %xtraiter.epil.1, 0
  br i1 %lcmp.mod.epil.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.1, label %for.body8.epil.epil.1.preheader

for.body8.epil.epil.1.preheader:                  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1
  br label %for.body8.epil.epil.1

for.body8.epil.epil.1:                            ; preds = %for.body8.epil.epil.1.preheader, %for.body8.epil.epil.1
  %indvars.iv.epil.epil.1 = phi i64 [ %indvars.iv.next.epil.epil.1, %for.body8.epil.epil.1 ], [ %indvars.iv.unr.epil.1, %for.body8.epil.epil.1.preheader ]
  %add53.epil.epil.1 = phi float [ %add.epil.epil.1, %for.body8.epil.epil.1 ], [ %add53.unr.epil.1, %for.body8.epil.epil.1.preheader ]
  %epil.iter.epil.1 = phi i32 [ %epil.iter.sub.epil.1, %for.body8.epil.epil.1 ], [ %xtraiter.epil.1, %for.body8.epil.epil.1.preheader ]
  %arrayidx10.epil.epil.1 = getelementptr inbounds float, float* %arrayidx.1, i64 %indvars.iv.epil.epil.1
  %246 = load float, float* %arrayidx10.epil.epil.1, align 4, !tbaa !3
  %247 = mul nuw nsw i64 %indvars.iv.epil.epil.1, %0
  %arrayidx12.epil.epil.1 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.1
  %arrayidx14.epil.epil.1 = getelementptr inbounds float, float* %arrayidx12.epil.epil.1, i64 %247
  %248 = load float, float* %arrayidx14.epil.epil.1, align 4, !tbaa !3
  %mul.epil.epil.1 = fmul float %246, %248
  %add.epil.epil.1 = fadd float %add53.epil.epil.1, %mul.epil.epil.1
  %indvars.iv.next.epil.epil.1 = add nuw nsw i64 %indvars.iv.epil.epil.1, 1
  %epil.iter.sub.epil.1 = add i32 %epil.iter.epil.1, -1
  %epil.iter.cmp.epil.1.not = icmp eq i32 %epil.iter.sub.epil.1, 0
  br i1 %epil.iter.cmp.epil.1.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.1.loopexit, label %for.body8.epil.epil.1, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.epil.1.loopexit: ; preds = %for.body8.epil.epil.1
  %add.epil.epil.1.lcssa = phi float [ %add.epil.epil.1, %for.body8.epil.epil.1 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.epil.1

for.cond5.for.cond.cleanup7_crit_edge.epil.1:     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil.1.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1
  %add.lcssa.epil.1 = phi float [ %add.lcssa.ph.epil.1, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.1 ], [ %add.epil.epil.1.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.epil.1.loopexit ]
  store float %add.lcssa.epil.1, float* %arrayidx18.epil.1, align 4, !tbaa !3
  %indvars.iv.next56.epil.1 = add nuw nsw i64 %indvars.iv55.epil.1, 1
  %epil.iter69.sub.1 = add i32 %epil.iter69.1, -1
  %epil.iter69.cmp.1.not = icmp eq i32 %epil.iter69.sub.1, 0
  br i1 %epil.iter69.cmp.1.not, label %for.cond5.preheader.lr.ph.2.loopexit, label %for.cond5.preheader.epil.1, !llvm.loop !12

for.cond5.preheader.lr.ph.2.loopexit:             ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil.1
  br label %for.cond5.preheader.lr.ph.2

for.cond5.preheader.lr.ph.2:                      ; preds = %for.cond5.preheader.lr.ph.2.loopexit, %for.cond.cleanup3.loopexit.unr-lcssa.1
  %indvars.iv.next95.1 = or i64 %indvars.iv94, 2
  %249 = mul nuw nsw i64 %indvars.iv.next95.1, %0
  %arrayidx.2 = getelementptr inbounds float, float* %a, i64 %249
  %arrayidx16.2 = getelementptr inbounds float, float* %c, i64 %249
  %xtraiter58.2 = and i32 %n, 3
  %250 = icmp ult i32 %1, 3
  br i1 %250, label %for.cond.cleanup3.loopexit.unr-lcssa.2, label %for.cond5.preheader.lr.ph.new.2

for.cond5.preheader.lr.ph.new.2:                  ; preds = %for.cond5.preheader.lr.ph.2
  %unroll_iter71.2 = and i32 %n, -4
  br label %for.cond5.preheader.2

for.cond5.preheader.2:                            ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.2, %for.cond5.preheader.lr.ph.new.2
  %indvars.iv55.2 = phi i64 [ 0, %for.cond5.preheader.lr.ph.new.2 ], [ %indvars.iv.next56.3.2, %for.cond5.for.cond.cleanup7_crit_edge.3.2 ]
  %niter72.2 = phi i32 [ %unroll_iter71.2, %for.cond5.preheader.lr.ph.new.2 ], [ %niter72.nsub.3.2, %for.cond5.for.cond.cleanup7_crit_edge.3.2 ]
  %arrayidx18.2241 = getelementptr inbounds float, float* %arrayidx16.2, i64 %indvars.iv55.2
  %arrayidx18.promoted.2242 = load float, float* %arrayidx18.2241, align 4, !tbaa !3
  %xtraiter.2244 = and i32 %n, 3
  %251 = icmp ult i32 %1, 3
  br i1 %251, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289, label %for.body8.lr.ph.new.2247

for.body8.lr.ph.new.2247:                         ; preds = %for.cond5.preheader.2
  %unroll_iter.2246 = and i32 %n, -4
  br label %for.body8.2280

for.body8.2280:                                   ; preds = %for.body8.2280, %for.body8.lr.ph.new.2247
  %indvars.iv.2248 = phi i64 [ 0, %for.body8.lr.ph.new.2247 ], [ %indvars.iv.next.3.2277, %for.body8.2280 ]
  %add53.2249 = phi float [ %arrayidx18.promoted.2242, %for.body8.lr.ph.new.2247 ], [ %add.3.2276, %for.body8.2280 ]
  %niter.2250 = phi i32 [ %unroll_iter.2246, %for.body8.lr.ph.new.2247 ], [ %niter.nsub.3.2278, %for.body8.2280 ]
  %arrayidx10.2251 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.2248
  %252 = load float, float* %arrayidx10.2251, align 4, !tbaa !3
  %253 = mul nuw nsw i64 %indvars.iv.2248, %0
  %arrayidx12.2252 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.2
  %arrayidx14.2253 = getelementptr inbounds float, float* %arrayidx12.2252, i64 %253
  %254 = load float, float* %arrayidx14.2253, align 4, !tbaa !3
  %mul.2254 = fmul float %252, %254
  %add.2255 = fadd float %add53.2249, %mul.2254
  %indvars.iv.next.2256 = or i64 %indvars.iv.2248, 1
  %arrayidx10.1.2258 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.2256
  %255 = load float, float* %arrayidx10.1.2258, align 4, !tbaa !3
  %256 = mul nuw nsw i64 %indvars.iv.next.2256, %0
  %arrayidx12.1.2259 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.2
  %arrayidx14.1.2260 = getelementptr inbounds float, float* %arrayidx12.1.2259, i64 %256
  %257 = load float, float* %arrayidx14.1.2260, align 4, !tbaa !3
  %mul.1.2261 = fmul float %255, %257
  %add.1.2262 = fadd float %add.2255, %mul.1.2261
  %indvars.iv.next.1.2263 = or i64 %indvars.iv.2248, 2
  %arrayidx10.2.2265 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.1.2263
  %258 = load float, float* %arrayidx10.2.2265, align 4, !tbaa !3
  %259 = mul nuw nsw i64 %indvars.iv.next.1.2263, %0
  %arrayidx12.2.2266 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.2
  %arrayidx14.2.2267 = getelementptr inbounds float, float* %arrayidx12.2.2266, i64 %259
  %260 = load float, float* %arrayidx14.2.2267, align 4, !tbaa !3
  %mul.2.2268 = fmul float %258, %260
  %add.2.2269 = fadd float %add.1.2262, %mul.2.2268
  %indvars.iv.next.2.2270 = or i64 %indvars.iv.2248, 3
  %arrayidx10.3.2272 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.2.2270
  %261 = load float, float* %arrayidx10.3.2272, align 4, !tbaa !3
  %262 = mul nuw nsw i64 %indvars.iv.next.2.2270, %0
  %arrayidx12.3.2273 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.2
  %arrayidx14.3.2274 = getelementptr inbounds float, float* %arrayidx12.3.2273, i64 %262
  %263 = load float, float* %arrayidx14.3.2274, align 4, !tbaa !3
  %mul.3.2275 = fmul float %261, %263
  %add.3.2276 = fadd float %add.2.2269, %mul.3.2275
  %indvars.iv.next.3.2277 = add nuw nsw i64 %indvars.iv.2248, 4
  %niter.nsub.3.2278 = add i32 %niter.2250, -4
  %niter.ncmp.3.2279.not = icmp eq i32 %niter.nsub.3.2278, 0
  br i1 %niter.ncmp.3.2279.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289.loopexit, label %for.body8.2280, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289.loopexit: ; preds = %for.body8.2280
  %add.3.2276.lcssa = phi float [ %add.3.2276, %for.body8.2280 ]
  %indvars.iv.next.3.2277.lcssa = phi i64 [ %indvars.iv.next.3.2277, %for.body8.2280 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289.loopexit, %for.cond5.preheader.2
  %add.lcssa.ph.2285 = phi float [ undef, %for.cond5.preheader.2 ], [ %add.3.2276.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289.loopexit ]
  %indvars.iv.unr.2286 = phi i64 [ 0, %for.cond5.preheader.2 ], [ %indvars.iv.next.3.2277.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289.loopexit ]
  %add53.unr.2287 = phi float [ %arrayidx18.promoted.2242, %for.cond5.preheader.2 ], [ %add.3.2276.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289.loopexit ]
  %lcmp.mod.2288.not = icmp eq i32 %xtraiter.2244, 0
  br i1 %lcmp.mod.2288.not, label %for.cond5.for.cond.cleanup7_crit_edge.2306, label %for.body8.epil.2302.preheader

for.body8.epil.2302.preheader:                    ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289
  br label %for.body8.epil.2302

for.body8.epil.2302:                              ; preds = %for.body8.epil.2302.preheader, %for.body8.epil.2302
  %indvars.iv.epil.2291 = phi i64 [ %indvars.iv.next.epil.2299, %for.body8.epil.2302 ], [ %indvars.iv.unr.2286, %for.body8.epil.2302.preheader ]
  %add53.epil.2292 = phi float [ %add.epil.2298, %for.body8.epil.2302 ], [ %add53.unr.2287, %for.body8.epil.2302.preheader ]
  %epil.iter.2293 = phi i32 [ %epil.iter.sub.2300, %for.body8.epil.2302 ], [ %xtraiter.2244, %for.body8.epil.2302.preheader ]
  %arrayidx10.epil.2294 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.epil.2291
  %264 = load float, float* %arrayidx10.epil.2294, align 4, !tbaa !3
  %265 = mul nuw nsw i64 %indvars.iv.epil.2291, %0
  %arrayidx12.epil.2295 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.2
  %arrayidx14.epil.2296 = getelementptr inbounds float, float* %arrayidx12.epil.2295, i64 %265
  %266 = load float, float* %arrayidx14.epil.2296, align 4, !tbaa !3
  %mul.epil.2297 = fmul float %264, %266
  %add.epil.2298 = fadd float %add53.epil.2292, %mul.epil.2297
  %indvars.iv.next.epil.2299 = add nuw nsw i64 %indvars.iv.epil.2291, 1
  %epil.iter.sub.2300 = add i32 %epil.iter.2293, -1
  %epil.iter.cmp.2301.not = icmp eq i32 %epil.iter.sub.2300, 0
  br i1 %epil.iter.cmp.2301.not, label %for.cond5.for.cond.cleanup7_crit_edge.2306.loopexit, label %for.body8.epil.2302, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.2306.loopexit: ; preds = %for.body8.epil.2302
  %add.epil.2298.lcssa = phi float [ %add.epil.2298, %for.body8.epil.2302 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.2306

for.cond5.for.cond.cleanup7_crit_edge.2306:       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2306.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289
  %add.lcssa.2305 = phi float [ %add.lcssa.ph.2285, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2289 ], [ %add.epil.2298.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.2306.loopexit ]
  store float %add.lcssa.2305, float* %arrayidx18.2241, align 4, !tbaa !3
  %indvars.iv.next56.2307 = or i64 %indvars.iv55.2, 1
  %arrayidx18.1.2 = getelementptr inbounds float, float* %arrayidx16.2, i64 %indvars.iv.next56.2307
  %arrayidx18.promoted.1.2 = load float, float* %arrayidx18.1.2, align 4, !tbaa !3
  %xtraiter.1.2 = and i32 %n, 3
  %267 = icmp ult i32 %1, 3
  br i1 %267, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2, label %for.body8.lr.ph.new.1.2

for.body8.lr.ph.new.1.2:                          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2306
  %unroll_iter.1.2 = and i32 %n, -4
  br label %for.body8.1.2

for.body8.1.2:                                    ; preds = %for.body8.1.2, %for.body8.lr.ph.new.1.2
  %indvars.iv.1.2 = phi i64 [ 0, %for.body8.lr.ph.new.1.2 ], [ %indvars.iv.next.3.1.2, %for.body8.1.2 ]
  %add53.1.2 = phi float [ %arrayidx18.promoted.1.2, %for.body8.lr.ph.new.1.2 ], [ %add.3.1.2, %for.body8.1.2 ]
  %niter.1.2 = phi i32 [ %unroll_iter.1.2, %for.body8.lr.ph.new.1.2 ], [ %niter.nsub.3.1.2, %for.body8.1.2 ]
  %arrayidx10.173.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.1.2
  %268 = load float, float* %arrayidx10.173.2, align 4, !tbaa !3
  %269 = mul nuw nsw i64 %indvars.iv.1.2, %0
  %arrayidx12.174.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2307
  %arrayidx14.175.2 = getelementptr inbounds float, float* %arrayidx12.174.2, i64 %269
  %270 = load float, float* %arrayidx14.175.2, align 4, !tbaa !3
  %mul.176.2 = fmul float %268, %270
  %add.177.2 = fadd float %add53.1.2, %mul.176.2
  %indvars.iv.next.178.2 = or i64 %indvars.iv.1.2, 1
  %arrayidx10.1.1.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.178.2
  %271 = load float, float* %arrayidx10.1.1.2, align 4, !tbaa !3
  %272 = mul nuw nsw i64 %indvars.iv.next.178.2, %0
  %arrayidx12.1.1.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2307
  %arrayidx14.1.1.2 = getelementptr inbounds float, float* %arrayidx12.1.1.2, i64 %272
  %273 = load float, float* %arrayidx14.1.1.2, align 4, !tbaa !3
  %mul.1.1.2 = fmul float %271, %273
  %add.1.1.2 = fadd float %add.177.2, %mul.1.1.2
  %indvars.iv.next.1.1.2 = or i64 %indvars.iv.1.2, 2
  %arrayidx10.2.1.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.1.1.2
  %274 = load float, float* %arrayidx10.2.1.2, align 4, !tbaa !3
  %275 = mul nuw nsw i64 %indvars.iv.next.1.1.2, %0
  %arrayidx12.2.1.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2307
  %arrayidx14.2.1.2 = getelementptr inbounds float, float* %arrayidx12.2.1.2, i64 %275
  %276 = load float, float* %arrayidx14.2.1.2, align 4, !tbaa !3
  %mul.2.1.2 = fmul float %274, %276
  %add.2.1.2 = fadd float %add.1.1.2, %mul.2.1.2
  %indvars.iv.next.2.1.2 = or i64 %indvars.iv.1.2, 3
  %arrayidx10.3.1.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.2.1.2
  %277 = load float, float* %arrayidx10.3.1.2, align 4, !tbaa !3
  %278 = mul nuw nsw i64 %indvars.iv.next.2.1.2, %0
  %arrayidx12.3.1.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2307
  %arrayidx14.3.1.2 = getelementptr inbounds float, float* %arrayidx12.3.1.2, i64 %278
  %279 = load float, float* %arrayidx14.3.1.2, align 4, !tbaa !3
  %mul.3.1.2 = fmul float %277, %279
  %add.3.1.2 = fadd float %add.2.1.2, %mul.3.1.2
  %indvars.iv.next.3.1.2 = add nuw nsw i64 %indvars.iv.1.2, 4
  %niter.nsub.3.1.2 = add i32 %niter.1.2, -4
  %niter.ncmp.3.1.2.not = icmp eq i32 %niter.nsub.3.1.2, 0
  br i1 %niter.ncmp.3.1.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2.loopexit, label %for.body8.1.2, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2.loopexit: ; preds = %for.body8.1.2
  %add.3.1.2.lcssa = phi float [ %add.3.1.2, %for.body8.1.2 ]
  %indvars.iv.next.3.1.2.lcssa = phi i64 [ %indvars.iv.next.3.1.2, %for.body8.1.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.2306
  %add.lcssa.ph.1.2 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.2306 ], [ %add.3.1.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2.loopexit ]
  %indvars.iv.unr.1.2 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.2306 ], [ %indvars.iv.next.3.1.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2.loopexit ]
  %add53.unr.1.2 = phi float [ %arrayidx18.promoted.1.2, %for.cond5.for.cond.cleanup7_crit_edge.2306 ], [ %add.3.1.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2.loopexit ]
  %lcmp.mod.1.2.not = icmp eq i32 %xtraiter.1.2, 0
  br i1 %lcmp.mod.1.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.2, label %for.body8.epil.1.2.preheader

for.body8.epil.1.2.preheader:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2
  br label %for.body8.epil.1.2

for.body8.epil.1.2:                               ; preds = %for.body8.epil.1.2.preheader, %for.body8.epil.1.2
  %indvars.iv.epil.1.2 = phi i64 [ %indvars.iv.next.epil.1.2, %for.body8.epil.1.2 ], [ %indvars.iv.unr.1.2, %for.body8.epil.1.2.preheader ]
  %add53.epil.1.2 = phi float [ %add.epil.1.2, %for.body8.epil.1.2 ], [ %add53.unr.1.2, %for.body8.epil.1.2.preheader ]
  %epil.iter.1.2 = phi i32 [ %epil.iter.sub.1.2, %for.body8.epil.1.2 ], [ %xtraiter.1.2, %for.body8.epil.1.2.preheader ]
  %arrayidx10.epil.1.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.epil.1.2
  %280 = load float, float* %arrayidx10.epil.1.2, align 4, !tbaa !3
  %281 = mul nuw nsw i64 %indvars.iv.epil.1.2, %0
  %arrayidx12.epil.1.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2307
  %arrayidx14.epil.1.2 = getelementptr inbounds float, float* %arrayidx12.epil.1.2, i64 %281
  %282 = load float, float* %arrayidx14.epil.1.2, align 4, !tbaa !3
  %mul.epil.1.2 = fmul float %280, %282
  %add.epil.1.2 = fadd float %add53.epil.1.2, %mul.epil.1.2
  %indvars.iv.next.epil.1.2 = add nuw nsw i64 %indvars.iv.epil.1.2, 1
  %epil.iter.sub.1.2 = add i32 %epil.iter.1.2, -1
  %epil.iter.cmp.1.2.not = icmp eq i32 %epil.iter.sub.1.2, 0
  br i1 %epil.iter.cmp.1.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.2.loopexit, label %for.body8.epil.1.2, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.1.2.loopexit: ; preds = %for.body8.epil.1.2
  %add.epil.1.2.lcssa = phi float [ %add.epil.1.2, %for.body8.epil.1.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.1.2

for.cond5.for.cond.cleanup7_crit_edge.1.2:        ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.2.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2
  %add.lcssa.1.2 = phi float [ %add.lcssa.ph.1.2, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.2 ], [ %add.epil.1.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.1.2.loopexit ]
  store float %add.lcssa.1.2, float* %arrayidx18.1.2, align 4, !tbaa !3
  %indvars.iv.next56.1.2 = or i64 %indvars.iv55.2, 2
  %arrayidx18.2.2 = getelementptr inbounds float, float* %arrayidx16.2, i64 %indvars.iv.next56.1.2
  %arrayidx18.promoted.2.2 = load float, float* %arrayidx18.2.2, align 4, !tbaa !3
  %xtraiter.2.2 = and i32 %n, 3
  %283 = icmp ult i32 %1, 3
  br i1 %283, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2, label %for.body8.lr.ph.new.2.2

for.body8.lr.ph.new.2.2:                          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.2
  %unroll_iter.2.2 = and i32 %n, -4
  br label %for.body8.2.2

for.body8.2.2:                                    ; preds = %for.body8.2.2, %for.body8.lr.ph.new.2.2
  %indvars.iv.2.2 = phi i64 [ 0, %for.body8.lr.ph.new.2.2 ], [ %indvars.iv.next.3.2.2, %for.body8.2.2 ]
  %add53.2.2 = phi float [ %arrayidx18.promoted.2.2, %for.body8.lr.ph.new.2.2 ], [ %add.3.2.2, %for.body8.2.2 ]
  %niter.2.2 = phi i32 [ %unroll_iter.2.2, %for.body8.lr.ph.new.2.2 ], [ %niter.nsub.3.2.2, %for.body8.2.2 ]
  %arrayidx10.280.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.2.2
  %284 = load float, float* %arrayidx10.280.2, align 4, !tbaa !3
  %285 = mul nuw nsw i64 %indvars.iv.2.2, %0
  %arrayidx12.281.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.2
  %arrayidx14.282.2 = getelementptr inbounds float, float* %arrayidx12.281.2, i64 %285
  %286 = load float, float* %arrayidx14.282.2, align 4, !tbaa !3
  %mul.283.2 = fmul float %284, %286
  %add.284.2 = fadd float %add53.2.2, %mul.283.2
  %indvars.iv.next.285.2 = or i64 %indvars.iv.2.2, 1
  %arrayidx10.1.2.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.285.2
  %287 = load float, float* %arrayidx10.1.2.2, align 4, !tbaa !3
  %288 = mul nuw nsw i64 %indvars.iv.next.285.2, %0
  %arrayidx12.1.2.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.2
  %arrayidx14.1.2.2 = getelementptr inbounds float, float* %arrayidx12.1.2.2, i64 %288
  %289 = load float, float* %arrayidx14.1.2.2, align 4, !tbaa !3
  %mul.1.2.2 = fmul float %287, %289
  %add.1.2.2 = fadd float %add.284.2, %mul.1.2.2
  %indvars.iv.next.1.2.2 = or i64 %indvars.iv.2.2, 2
  %arrayidx10.2.2.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.1.2.2
  %290 = load float, float* %arrayidx10.2.2.2, align 4, !tbaa !3
  %291 = mul nuw nsw i64 %indvars.iv.next.1.2.2, %0
  %arrayidx12.2.2.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.2
  %arrayidx14.2.2.2 = getelementptr inbounds float, float* %arrayidx12.2.2.2, i64 %291
  %292 = load float, float* %arrayidx14.2.2.2, align 4, !tbaa !3
  %mul.2.2.2 = fmul float %290, %292
  %add.2.2.2 = fadd float %add.1.2.2, %mul.2.2.2
  %indvars.iv.next.2.2.2 = or i64 %indvars.iv.2.2, 3
  %arrayidx10.3.2.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.2.2.2
  %293 = load float, float* %arrayidx10.3.2.2, align 4, !tbaa !3
  %294 = mul nuw nsw i64 %indvars.iv.next.2.2.2, %0
  %arrayidx12.3.2.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.2
  %arrayidx14.3.2.2 = getelementptr inbounds float, float* %arrayidx12.3.2.2, i64 %294
  %295 = load float, float* %arrayidx14.3.2.2, align 4, !tbaa !3
  %mul.3.2.2 = fmul float %293, %295
  %add.3.2.2 = fadd float %add.2.2.2, %mul.3.2.2
  %indvars.iv.next.3.2.2 = add nuw nsw i64 %indvars.iv.2.2, 4
  %niter.nsub.3.2.2 = add i32 %niter.2.2, -4
  %niter.ncmp.3.2.2.not = icmp eq i32 %niter.nsub.3.2.2, 0
  br i1 %niter.ncmp.3.2.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2.loopexit, label %for.body8.2.2, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2.loopexit: ; preds = %for.body8.2.2
  %add.3.2.2.lcssa = phi float [ %add.3.2.2, %for.body8.2.2 ]
  %indvars.iv.next.3.2.2.lcssa = phi i64 [ %indvars.iv.next.3.2.2, %for.body8.2.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.1.2
  %add.lcssa.ph.2.2 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.1.2 ], [ %add.3.2.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2.loopexit ]
  %indvars.iv.unr.2.2 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.1.2 ], [ %indvars.iv.next.3.2.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2.loopexit ]
  %add53.unr.2.2 = phi float [ %arrayidx18.promoted.2.2, %for.cond5.for.cond.cleanup7_crit_edge.1.2 ], [ %add.3.2.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2.loopexit ]
  %lcmp.mod.2.2.not = icmp eq i32 %xtraiter.2.2, 0
  br i1 %lcmp.mod.2.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.2.2, label %for.body8.epil.2.2.preheader

for.body8.epil.2.2.preheader:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2
  br label %for.body8.epil.2.2

for.body8.epil.2.2:                               ; preds = %for.body8.epil.2.2.preheader, %for.body8.epil.2.2
  %indvars.iv.epil.2.2 = phi i64 [ %indvars.iv.next.epil.2.2, %for.body8.epil.2.2 ], [ %indvars.iv.unr.2.2, %for.body8.epil.2.2.preheader ]
  %add53.epil.2.2 = phi float [ %add.epil.2.2, %for.body8.epil.2.2 ], [ %add53.unr.2.2, %for.body8.epil.2.2.preheader ]
  %epil.iter.2.2 = phi i32 [ %epil.iter.sub.2.2, %for.body8.epil.2.2 ], [ %xtraiter.2.2, %for.body8.epil.2.2.preheader ]
  %arrayidx10.epil.2.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.epil.2.2
  %296 = load float, float* %arrayidx10.epil.2.2, align 4, !tbaa !3
  %297 = mul nuw nsw i64 %indvars.iv.epil.2.2, %0
  %arrayidx12.epil.2.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.2
  %arrayidx14.epil.2.2 = getelementptr inbounds float, float* %arrayidx12.epil.2.2, i64 %297
  %298 = load float, float* %arrayidx14.epil.2.2, align 4, !tbaa !3
  %mul.epil.2.2 = fmul float %296, %298
  %add.epil.2.2 = fadd float %add53.epil.2.2, %mul.epil.2.2
  %indvars.iv.next.epil.2.2 = add nuw nsw i64 %indvars.iv.epil.2.2, 1
  %epil.iter.sub.2.2 = add i32 %epil.iter.2.2, -1
  %epil.iter.cmp.2.2.not = icmp eq i32 %epil.iter.sub.2.2, 0
  br i1 %epil.iter.cmp.2.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.2.2.loopexit, label %for.body8.epil.2.2, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.2.2.loopexit: ; preds = %for.body8.epil.2.2
  %add.epil.2.2.lcssa = phi float [ %add.epil.2.2, %for.body8.epil.2.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.2.2

for.cond5.for.cond.cleanup7_crit_edge.2.2:        ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2.2.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2
  %add.lcssa.2.2 = phi float [ %add.lcssa.ph.2.2, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.2 ], [ %add.epil.2.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.2.2.loopexit ]
  store float %add.lcssa.2.2, float* %arrayidx18.2.2, align 4, !tbaa !3
  %indvars.iv.next56.2.2 = or i64 %indvars.iv55.2, 3
  %arrayidx18.3.2 = getelementptr inbounds float, float* %arrayidx16.2, i64 %indvars.iv.next56.2.2
  %arrayidx18.promoted.3.2 = load float, float* %arrayidx18.3.2, align 4, !tbaa !3
  %xtraiter.3.2 = and i32 %n, 3
  %299 = icmp ult i32 %1, 3
  br i1 %299, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2, label %for.body8.lr.ph.new.3.2

for.body8.lr.ph.new.3.2:                          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2.2
  %unroll_iter.3.2 = and i32 %n, -4
  br label %for.body8.3.2

for.body8.3.2:                                    ; preds = %for.body8.3.2, %for.body8.lr.ph.new.3.2
  %indvars.iv.3.2 = phi i64 [ 0, %for.body8.lr.ph.new.3.2 ], [ %indvars.iv.next.3.3.2, %for.body8.3.2 ]
  %add53.3.2 = phi float [ %arrayidx18.promoted.3.2, %for.body8.lr.ph.new.3.2 ], [ %add.3.3.2, %for.body8.3.2 ]
  %niter.3.2 = phi i32 [ %unroll_iter.3.2, %for.body8.lr.ph.new.3.2 ], [ %niter.nsub.3.3.2, %for.body8.3.2 ]
  %arrayidx10.387.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.3.2
  %300 = load float, float* %arrayidx10.387.2, align 4, !tbaa !3
  %301 = mul nuw nsw i64 %indvars.iv.3.2, %0
  %arrayidx12.388.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.2
  %arrayidx14.389.2 = getelementptr inbounds float, float* %arrayidx12.388.2, i64 %301
  %302 = load float, float* %arrayidx14.389.2, align 4, !tbaa !3
  %mul.390.2 = fmul float %300, %302
  %add.391.2 = fadd float %add53.3.2, %mul.390.2
  %indvars.iv.next.392.2 = or i64 %indvars.iv.3.2, 1
  %arrayidx10.1.3.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.392.2
  %303 = load float, float* %arrayidx10.1.3.2, align 4, !tbaa !3
  %304 = mul nuw nsw i64 %indvars.iv.next.392.2, %0
  %arrayidx12.1.3.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.2
  %arrayidx14.1.3.2 = getelementptr inbounds float, float* %arrayidx12.1.3.2, i64 %304
  %305 = load float, float* %arrayidx14.1.3.2, align 4, !tbaa !3
  %mul.1.3.2 = fmul float %303, %305
  %add.1.3.2 = fadd float %add.391.2, %mul.1.3.2
  %indvars.iv.next.1.3.2 = or i64 %indvars.iv.3.2, 2
  %arrayidx10.2.3.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.1.3.2
  %306 = load float, float* %arrayidx10.2.3.2, align 4, !tbaa !3
  %307 = mul nuw nsw i64 %indvars.iv.next.1.3.2, %0
  %arrayidx12.2.3.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.2
  %arrayidx14.2.3.2 = getelementptr inbounds float, float* %arrayidx12.2.3.2, i64 %307
  %308 = load float, float* %arrayidx14.2.3.2, align 4, !tbaa !3
  %mul.2.3.2 = fmul float %306, %308
  %add.2.3.2 = fadd float %add.1.3.2, %mul.2.3.2
  %indvars.iv.next.2.3.2 = or i64 %indvars.iv.3.2, 3
  %arrayidx10.3.3.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.2.3.2
  %309 = load float, float* %arrayidx10.3.3.2, align 4, !tbaa !3
  %310 = mul nuw nsw i64 %indvars.iv.next.2.3.2, %0
  %arrayidx12.3.3.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.2
  %arrayidx14.3.3.2 = getelementptr inbounds float, float* %arrayidx12.3.3.2, i64 %310
  %311 = load float, float* %arrayidx14.3.3.2, align 4, !tbaa !3
  %mul.3.3.2 = fmul float %309, %311
  %add.3.3.2 = fadd float %add.2.3.2, %mul.3.3.2
  %indvars.iv.next.3.3.2 = add nuw nsw i64 %indvars.iv.3.2, 4
  %niter.nsub.3.3.2 = add i32 %niter.3.2, -4
  %niter.ncmp.3.3.2.not = icmp eq i32 %niter.nsub.3.3.2, 0
  br i1 %niter.ncmp.3.3.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2.loopexit, label %for.body8.3.2, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2.loopexit: ; preds = %for.body8.3.2
  %add.3.3.2.lcssa = phi float [ %add.3.3.2, %for.body8.3.2 ]
  %indvars.iv.next.3.3.2.lcssa = phi i64 [ %indvars.iv.next.3.3.2, %for.body8.3.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.2.2
  %add.lcssa.ph.3.2 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.2.2 ], [ %add.3.3.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2.loopexit ]
  %indvars.iv.unr.3.2 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.2.2 ], [ %indvars.iv.next.3.3.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2.loopexit ]
  %add53.unr.3.2 = phi float [ %arrayidx18.promoted.3.2, %for.cond5.for.cond.cleanup7_crit_edge.2.2 ], [ %add.3.3.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2.loopexit ]
  %lcmp.mod.3.2.not = icmp eq i32 %xtraiter.3.2, 0
  br i1 %lcmp.mod.3.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.3.2, label %for.body8.epil.3.2.preheader

for.body8.epil.3.2.preheader:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2
  br label %for.body8.epil.3.2

for.body8.epil.3.2:                               ; preds = %for.body8.epil.3.2.preheader, %for.body8.epil.3.2
  %indvars.iv.epil.3.2 = phi i64 [ %indvars.iv.next.epil.3.2, %for.body8.epil.3.2 ], [ %indvars.iv.unr.3.2, %for.body8.epil.3.2.preheader ]
  %add53.epil.3.2 = phi float [ %add.epil.3.2, %for.body8.epil.3.2 ], [ %add53.unr.3.2, %for.body8.epil.3.2.preheader ]
  %epil.iter.3.2 = phi i32 [ %epil.iter.sub.3.2, %for.body8.epil.3.2 ], [ %xtraiter.3.2, %for.body8.epil.3.2.preheader ]
  %arrayidx10.epil.3.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.epil.3.2
  %312 = load float, float* %arrayidx10.epil.3.2, align 4, !tbaa !3
  %313 = mul nuw nsw i64 %indvars.iv.epil.3.2, %0
  %arrayidx12.epil.3.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.2
  %arrayidx14.epil.3.2 = getelementptr inbounds float, float* %arrayidx12.epil.3.2, i64 %313
  %314 = load float, float* %arrayidx14.epil.3.2, align 4, !tbaa !3
  %mul.epil.3.2 = fmul float %312, %314
  %add.epil.3.2 = fadd float %add53.epil.3.2, %mul.epil.3.2
  %indvars.iv.next.epil.3.2 = add nuw nsw i64 %indvars.iv.epil.3.2, 1
  %epil.iter.sub.3.2 = add i32 %epil.iter.3.2, -1
  %epil.iter.cmp.3.2.not = icmp eq i32 %epil.iter.sub.3.2, 0
  br i1 %epil.iter.cmp.3.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.3.2.loopexit, label %for.body8.epil.3.2, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.3.2.loopexit: ; preds = %for.body8.epil.3.2
  %add.epil.3.2.lcssa = phi float [ %add.epil.3.2, %for.body8.epil.3.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.3.2

for.cond5.for.cond.cleanup7_crit_edge.3.2:        ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.2.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2
  %add.lcssa.3.2 = phi float [ %add.lcssa.ph.3.2, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.2 ], [ %add.epil.3.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.3.2.loopexit ]
  store float %add.lcssa.3.2, float* %arrayidx18.3.2, align 4, !tbaa !3
  %indvars.iv.next56.3.2 = add nuw nsw i64 %indvars.iv55.2, 4
  %niter72.nsub.3.2 = add i32 %niter72.2, -4
  %niter72.ncmp.3.2.not = icmp eq i32 %niter72.nsub.3.2, 0
  br i1 %niter72.ncmp.3.2.not, label %for.cond.cleanup3.loopexit.unr-lcssa.2.loopexit, label %for.cond5.preheader.2, !llvm.loop !11

for.cond.cleanup3.loopexit.unr-lcssa.2.loopexit:  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.2
  %indvars.iv.next56.3.2.lcssa = phi i64 [ %indvars.iv.next56.3.2, %for.cond5.for.cond.cleanup7_crit_edge.3.2 ]
  br label %for.cond.cleanup3.loopexit.unr-lcssa.2

for.cond.cleanup3.loopexit.unr-lcssa.2:           ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.2.loopexit, %for.cond5.preheader.lr.ph.2
  %indvars.iv55.unr.2 = phi i64 [ 0, %for.cond5.preheader.lr.ph.2 ], [ %indvars.iv.next56.3.2.lcssa, %for.cond.cleanup3.loopexit.unr-lcssa.2.loopexit ]
  %lcmp.mod70.2.not = icmp eq i32 %xtraiter58.2, 0
  br i1 %lcmp.mod70.2.not, label %for.cond5.preheader.lr.ph.3, label %for.cond5.preheader.epil.2.preheader

for.cond5.preheader.epil.2.preheader:             ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.2
  br label %for.cond5.preheader.epil.2

for.cond5.preheader.epil.2:                       ; preds = %for.cond5.preheader.epil.2.preheader, %for.cond5.for.cond.cleanup7_crit_edge.epil.2
  %indvars.iv55.epil.2 = phi i64 [ %indvars.iv.next56.epil.2, %for.cond5.for.cond.cleanup7_crit_edge.epil.2 ], [ %indvars.iv55.unr.2, %for.cond5.preheader.epil.2.preheader ]
  %epil.iter69.2 = phi i32 [ %epil.iter69.sub.2, %for.cond5.for.cond.cleanup7_crit_edge.epil.2 ], [ %xtraiter58.2, %for.cond5.preheader.epil.2.preheader ]
  %arrayidx18.epil.2 = getelementptr inbounds float, float* %arrayidx16.2, i64 %indvars.iv55.epil.2
  %arrayidx18.promoted.epil.2 = load float, float* %arrayidx18.epil.2, align 4, !tbaa !3
  %xtraiter.epil.2 = and i32 %n, 3
  %315 = icmp ult i32 %1, 3
  br i1 %315, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2, label %for.body8.lr.ph.new.epil.2

for.body8.lr.ph.new.epil.2:                       ; preds = %for.cond5.preheader.epil.2
  %unroll_iter.epil.2 = and i32 %n, -4
  br label %for.body8.epil59.2

for.body8.epil59.2:                               ; preds = %for.body8.epil59.2, %for.body8.lr.ph.new.epil.2
  %indvars.iv.epil60.2 = phi i64 [ 0, %for.body8.lr.ph.new.epil.2 ], [ %indvars.iv.next.3.epil.2, %for.body8.epil59.2 ]
  %add53.epil61.2 = phi float [ %arrayidx18.promoted.epil.2, %for.body8.lr.ph.new.epil.2 ], [ %add.3.epil.2, %for.body8.epil59.2 ]
  %niter.epil.2 = phi i32 [ %unroll_iter.epil.2, %for.body8.lr.ph.new.epil.2 ], [ %niter.nsub.3.epil.2, %for.body8.epil59.2 ]
  %arrayidx10.epil62.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.epil60.2
  %316 = load float, float* %arrayidx10.epil62.2, align 4, !tbaa !3
  %317 = mul nuw nsw i64 %indvars.iv.epil60.2, %0
  %arrayidx12.epil63.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.2
  %arrayidx14.epil64.2 = getelementptr inbounds float, float* %arrayidx12.epil63.2, i64 %317
  %318 = load float, float* %arrayidx14.epil64.2, align 4, !tbaa !3
  %mul.epil65.2 = fmul float %316, %318
  %add.epil66.2 = fadd float %add53.epil61.2, %mul.epil65.2
  %indvars.iv.next.epil67.2 = or i64 %indvars.iv.epil60.2, 1
  %arrayidx10.1.epil.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.epil67.2
  %319 = load float, float* %arrayidx10.1.epil.2, align 4, !tbaa !3
  %320 = mul nuw nsw i64 %indvars.iv.next.epil67.2, %0
  %arrayidx12.1.epil.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.2
  %arrayidx14.1.epil.2 = getelementptr inbounds float, float* %arrayidx12.1.epil.2, i64 %320
  %321 = load float, float* %arrayidx14.1.epil.2, align 4, !tbaa !3
  %mul.1.epil.2 = fmul float %319, %321
  %add.1.epil.2 = fadd float %add.epil66.2, %mul.1.epil.2
  %indvars.iv.next.1.epil.2 = or i64 %indvars.iv.epil60.2, 2
  %arrayidx10.2.epil.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.1.epil.2
  %322 = load float, float* %arrayidx10.2.epil.2, align 4, !tbaa !3
  %323 = mul nuw nsw i64 %indvars.iv.next.1.epil.2, %0
  %arrayidx12.2.epil.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.2
  %arrayidx14.2.epil.2 = getelementptr inbounds float, float* %arrayidx12.2.epil.2, i64 %323
  %324 = load float, float* %arrayidx14.2.epil.2, align 4, !tbaa !3
  %mul.2.epil.2 = fmul float %322, %324
  %add.2.epil.2 = fadd float %add.1.epil.2, %mul.2.epil.2
  %indvars.iv.next.2.epil.2 = or i64 %indvars.iv.epil60.2, 3
  %arrayidx10.3.epil.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.next.2.epil.2
  %325 = load float, float* %arrayidx10.3.epil.2, align 4, !tbaa !3
  %326 = mul nuw nsw i64 %indvars.iv.next.2.epil.2, %0
  %arrayidx12.3.epil.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.2
  %arrayidx14.3.epil.2 = getelementptr inbounds float, float* %arrayidx12.3.epil.2, i64 %326
  %327 = load float, float* %arrayidx14.3.epil.2, align 4, !tbaa !3
  %mul.3.epil.2 = fmul float %325, %327
  %add.3.epil.2 = fadd float %add.2.epil.2, %mul.3.epil.2
  %indvars.iv.next.3.epil.2 = add nuw nsw i64 %indvars.iv.epil60.2, 4
  %niter.nsub.3.epil.2 = add i32 %niter.epil.2, -4
  %niter.ncmp.3.epil.2.not = icmp eq i32 %niter.nsub.3.epil.2, 0
  br i1 %niter.ncmp.3.epil.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2.loopexit, label %for.body8.epil59.2, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2.loopexit: ; preds = %for.body8.epil59.2
  %add.3.epil.2.lcssa = phi float [ %add.3.epil.2, %for.body8.epil59.2 ]
  %indvars.iv.next.3.epil.2.lcssa = phi i64 [ %indvars.iv.next.3.epil.2, %for.body8.epil59.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2.loopexit, %for.cond5.preheader.epil.2
  %add.lcssa.ph.epil.2 = phi float [ undef, %for.cond5.preheader.epil.2 ], [ %add.3.epil.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2.loopexit ]
  %indvars.iv.unr.epil.2 = phi i64 [ 0, %for.cond5.preheader.epil.2 ], [ %indvars.iv.next.3.epil.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2.loopexit ]
  %add53.unr.epil.2 = phi float [ %arrayidx18.promoted.epil.2, %for.cond5.preheader.epil.2 ], [ %add.3.epil.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2.loopexit ]
  %lcmp.mod.epil.2.not = icmp eq i32 %xtraiter.epil.2, 0
  br i1 %lcmp.mod.epil.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.2, label %for.body8.epil.epil.2.preheader

for.body8.epil.epil.2.preheader:                  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2
  br label %for.body8.epil.epil.2

for.body8.epil.epil.2:                            ; preds = %for.body8.epil.epil.2.preheader, %for.body8.epil.epil.2
  %indvars.iv.epil.epil.2 = phi i64 [ %indvars.iv.next.epil.epil.2, %for.body8.epil.epil.2 ], [ %indvars.iv.unr.epil.2, %for.body8.epil.epil.2.preheader ]
  %add53.epil.epil.2 = phi float [ %add.epil.epil.2, %for.body8.epil.epil.2 ], [ %add53.unr.epil.2, %for.body8.epil.epil.2.preheader ]
  %epil.iter.epil.2 = phi i32 [ %epil.iter.sub.epil.2, %for.body8.epil.epil.2 ], [ %xtraiter.epil.2, %for.body8.epil.epil.2.preheader ]
  %arrayidx10.epil.epil.2 = getelementptr inbounds float, float* %arrayidx.2, i64 %indvars.iv.epil.epil.2
  %328 = load float, float* %arrayidx10.epil.epil.2, align 4, !tbaa !3
  %329 = mul nuw nsw i64 %indvars.iv.epil.epil.2, %0
  %arrayidx12.epil.epil.2 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.2
  %arrayidx14.epil.epil.2 = getelementptr inbounds float, float* %arrayidx12.epil.epil.2, i64 %329
  %330 = load float, float* %arrayidx14.epil.epil.2, align 4, !tbaa !3
  %mul.epil.epil.2 = fmul float %328, %330
  %add.epil.epil.2 = fadd float %add53.epil.epil.2, %mul.epil.epil.2
  %indvars.iv.next.epil.epil.2 = add nuw nsw i64 %indvars.iv.epil.epil.2, 1
  %epil.iter.sub.epil.2 = add i32 %epil.iter.epil.2, -1
  %epil.iter.cmp.epil.2.not = icmp eq i32 %epil.iter.sub.epil.2, 0
  br i1 %epil.iter.cmp.epil.2.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.2.loopexit, label %for.body8.epil.epil.2, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.epil.2.loopexit: ; preds = %for.body8.epil.epil.2
  %add.epil.epil.2.lcssa = phi float [ %add.epil.epil.2, %for.body8.epil.epil.2 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.epil.2

for.cond5.for.cond.cleanup7_crit_edge.epil.2:     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil.2.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2
  %add.lcssa.epil.2 = phi float [ %add.lcssa.ph.epil.2, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.2 ], [ %add.epil.epil.2.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.epil.2.loopexit ]
  store float %add.lcssa.epil.2, float* %arrayidx18.epil.2, align 4, !tbaa !3
  %indvars.iv.next56.epil.2 = add nuw nsw i64 %indvars.iv55.epil.2, 1
  %epil.iter69.sub.2 = add i32 %epil.iter69.2, -1
  %epil.iter69.cmp.2.not = icmp eq i32 %epil.iter69.sub.2, 0
  br i1 %epil.iter69.cmp.2.not, label %for.cond5.preheader.lr.ph.3.loopexit, label %for.cond5.preheader.epil.2, !llvm.loop !12

for.cond5.preheader.lr.ph.3.loopexit:             ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil.2
  br label %for.cond5.preheader.lr.ph.3

for.cond5.preheader.lr.ph.3:                      ; preds = %for.cond5.preheader.lr.ph.3.loopexit, %for.cond.cleanup3.loopexit.unr-lcssa.2
  %indvars.iv.next95.2 = or i64 %indvars.iv94, 3
  %331 = mul nuw nsw i64 %indvars.iv.next95.2, %0
  %arrayidx.3 = getelementptr inbounds float, float* %a, i64 %331
  %arrayidx16.3 = getelementptr inbounds float, float* %c, i64 %331
  %xtraiter58.3 = and i32 %n, 3
  %332 = icmp ult i32 %1, 3
  br i1 %332, label %for.cond.cleanup3.loopexit.unr-lcssa.3, label %for.cond5.preheader.lr.ph.new.3

for.cond5.preheader.lr.ph.new.3:                  ; preds = %for.cond5.preheader.lr.ph.3
  %unroll_iter71.3 = and i32 %n, -4
  br label %for.cond5.preheader.3

for.cond5.preheader.3:                            ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.3, %for.cond5.preheader.lr.ph.new.3
  %indvars.iv55.3 = phi i64 [ 0, %for.cond5.preheader.lr.ph.new.3 ], [ %indvars.iv.next56.3.3, %for.cond5.for.cond.cleanup7_crit_edge.3.3 ]
  %niter72.3 = phi i32 [ %unroll_iter71.3, %for.cond5.preheader.lr.ph.new.3 ], [ %niter72.nsub.3.3, %for.cond5.for.cond.cleanup7_crit_edge.3.3 ]
  %arrayidx18.3310 = getelementptr inbounds float, float* %arrayidx16.3, i64 %indvars.iv55.3
  %arrayidx18.promoted.3311 = load float, float* %arrayidx18.3310, align 4, !tbaa !3
  %xtraiter.3313 = and i32 %n, 3
  %333 = icmp ult i32 %1, 3
  br i1 %333, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358, label %for.body8.lr.ph.new.3316

for.body8.lr.ph.new.3316:                         ; preds = %for.cond5.preheader.3
  %unroll_iter.3315 = and i32 %n, -4
  br label %for.body8.3349

for.body8.3349:                                   ; preds = %for.body8.3349, %for.body8.lr.ph.new.3316
  %indvars.iv.3317 = phi i64 [ 0, %for.body8.lr.ph.new.3316 ], [ %indvars.iv.next.3.3346, %for.body8.3349 ]
  %add53.3318 = phi float [ %arrayidx18.promoted.3311, %for.body8.lr.ph.new.3316 ], [ %add.3.3345, %for.body8.3349 ]
  %niter.3319 = phi i32 [ %unroll_iter.3315, %for.body8.lr.ph.new.3316 ], [ %niter.nsub.3.3347, %for.body8.3349 ]
  %arrayidx10.3320 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.3317
  %334 = load float, float* %arrayidx10.3320, align 4, !tbaa !3
  %335 = mul nuw nsw i64 %indvars.iv.3317, %0
  %arrayidx12.3321 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.3
  %arrayidx14.3322 = getelementptr inbounds float, float* %arrayidx12.3321, i64 %335
  %336 = load float, float* %arrayidx14.3322, align 4, !tbaa !3
  %mul.3323 = fmul float %334, %336
  %add.3324 = fadd float %add53.3318, %mul.3323
  %indvars.iv.next.3325 = or i64 %indvars.iv.3317, 1
  %arrayidx10.1.3327 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.3325
  %337 = load float, float* %arrayidx10.1.3327, align 4, !tbaa !3
  %338 = mul nuw nsw i64 %indvars.iv.next.3325, %0
  %arrayidx12.1.3328 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.3
  %arrayidx14.1.3329 = getelementptr inbounds float, float* %arrayidx12.1.3328, i64 %338
  %339 = load float, float* %arrayidx14.1.3329, align 4, !tbaa !3
  %mul.1.3330 = fmul float %337, %339
  %add.1.3331 = fadd float %add.3324, %mul.1.3330
  %indvars.iv.next.1.3332 = or i64 %indvars.iv.3317, 2
  %arrayidx10.2.3334 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.1.3332
  %340 = load float, float* %arrayidx10.2.3334, align 4, !tbaa !3
  %341 = mul nuw nsw i64 %indvars.iv.next.1.3332, %0
  %arrayidx12.2.3335 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.3
  %arrayidx14.2.3336 = getelementptr inbounds float, float* %arrayidx12.2.3335, i64 %341
  %342 = load float, float* %arrayidx14.2.3336, align 4, !tbaa !3
  %mul.2.3337 = fmul float %340, %342
  %add.2.3338 = fadd float %add.1.3331, %mul.2.3337
  %indvars.iv.next.2.3339 = or i64 %indvars.iv.3317, 3
  %arrayidx10.3.3341 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.2.3339
  %343 = load float, float* %arrayidx10.3.3341, align 4, !tbaa !3
  %344 = mul nuw nsw i64 %indvars.iv.next.2.3339, %0
  %arrayidx12.3.3342 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.3
  %arrayidx14.3.3343 = getelementptr inbounds float, float* %arrayidx12.3.3342, i64 %344
  %345 = load float, float* %arrayidx14.3.3343, align 4, !tbaa !3
  %mul.3.3344 = fmul float %343, %345
  %add.3.3345 = fadd float %add.2.3338, %mul.3.3344
  %indvars.iv.next.3.3346 = add nuw nsw i64 %indvars.iv.3317, 4
  %niter.nsub.3.3347 = add i32 %niter.3319, -4
  %niter.ncmp.3.3348.not = icmp eq i32 %niter.nsub.3.3347, 0
  br i1 %niter.ncmp.3.3348.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358.loopexit, label %for.body8.3349, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358.loopexit: ; preds = %for.body8.3349
  %add.3.3345.lcssa = phi float [ %add.3.3345, %for.body8.3349 ]
  %indvars.iv.next.3.3346.lcssa = phi i64 [ %indvars.iv.next.3.3346, %for.body8.3349 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358.loopexit, %for.cond5.preheader.3
  %add.lcssa.ph.3354 = phi float [ undef, %for.cond5.preheader.3 ], [ %add.3.3345.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358.loopexit ]
  %indvars.iv.unr.3355 = phi i64 [ 0, %for.cond5.preheader.3 ], [ %indvars.iv.next.3.3346.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358.loopexit ]
  %add53.unr.3356 = phi float [ %arrayidx18.promoted.3311, %for.cond5.preheader.3 ], [ %add.3.3345.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358.loopexit ]
  %lcmp.mod.3357.not = icmp eq i32 %xtraiter.3313, 0
  br i1 %lcmp.mod.3357.not, label %for.cond5.for.cond.cleanup7_crit_edge.3375, label %for.body8.epil.3371.preheader

for.body8.epil.3371.preheader:                    ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358
  br label %for.body8.epil.3371

for.body8.epil.3371:                              ; preds = %for.body8.epil.3371.preheader, %for.body8.epil.3371
  %indvars.iv.epil.3360 = phi i64 [ %indvars.iv.next.epil.3368, %for.body8.epil.3371 ], [ %indvars.iv.unr.3355, %for.body8.epil.3371.preheader ]
  %add53.epil.3361 = phi float [ %add.epil.3367, %for.body8.epil.3371 ], [ %add53.unr.3356, %for.body8.epil.3371.preheader ]
  %epil.iter.3362 = phi i32 [ %epil.iter.sub.3369, %for.body8.epil.3371 ], [ %xtraiter.3313, %for.body8.epil.3371.preheader ]
  %arrayidx10.epil.3363 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.epil.3360
  %346 = load float, float* %arrayidx10.epil.3363, align 4, !tbaa !3
  %347 = mul nuw nsw i64 %indvars.iv.epil.3360, %0
  %arrayidx12.epil.3364 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.3
  %arrayidx14.epil.3365 = getelementptr inbounds float, float* %arrayidx12.epil.3364, i64 %347
  %348 = load float, float* %arrayidx14.epil.3365, align 4, !tbaa !3
  %mul.epil.3366 = fmul float %346, %348
  %add.epil.3367 = fadd float %add53.epil.3361, %mul.epil.3366
  %indvars.iv.next.epil.3368 = add nuw nsw i64 %indvars.iv.epil.3360, 1
  %epil.iter.sub.3369 = add i32 %epil.iter.3362, -1
  %epil.iter.cmp.3370.not = icmp eq i32 %epil.iter.sub.3369, 0
  br i1 %epil.iter.cmp.3370.not, label %for.cond5.for.cond.cleanup7_crit_edge.3375.loopexit, label %for.body8.epil.3371, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.3375.loopexit: ; preds = %for.body8.epil.3371
  %add.epil.3367.lcssa = phi float [ %add.epil.3367, %for.body8.epil.3371 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.3375

for.cond5.for.cond.cleanup7_crit_edge.3375:       ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3375.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358
  %add.lcssa.3374 = phi float [ %add.lcssa.ph.3354, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3358 ], [ %add.epil.3367.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.3375.loopexit ]
  store float %add.lcssa.3374, float* %arrayidx18.3310, align 4, !tbaa !3
  %indvars.iv.next56.3376 = or i64 %indvars.iv55.3, 1
  %arrayidx18.1.3 = getelementptr inbounds float, float* %arrayidx16.3, i64 %indvars.iv.next56.3376
  %arrayidx18.promoted.1.3 = load float, float* %arrayidx18.1.3, align 4, !tbaa !3
  %xtraiter.1.3 = and i32 %n, 3
  %349 = icmp ult i32 %1, 3
  br i1 %349, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3, label %for.body8.lr.ph.new.1.3

for.body8.lr.ph.new.1.3:                          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3375
  %unroll_iter.1.3 = and i32 %n, -4
  br label %for.body8.1.3

for.body8.1.3:                                    ; preds = %for.body8.1.3, %for.body8.lr.ph.new.1.3
  %indvars.iv.1.3 = phi i64 [ 0, %for.body8.lr.ph.new.1.3 ], [ %indvars.iv.next.3.1.3, %for.body8.1.3 ]
  %add53.1.3 = phi float [ %arrayidx18.promoted.1.3, %for.body8.lr.ph.new.1.3 ], [ %add.3.1.3, %for.body8.1.3 ]
  %niter.1.3 = phi i32 [ %unroll_iter.1.3, %for.body8.lr.ph.new.1.3 ], [ %niter.nsub.3.1.3, %for.body8.1.3 ]
  %arrayidx10.173.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.1.3
  %350 = load float, float* %arrayidx10.173.3, align 4, !tbaa !3
  %351 = mul nuw nsw i64 %indvars.iv.1.3, %0
  %arrayidx12.174.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.3376
  %arrayidx14.175.3 = getelementptr inbounds float, float* %arrayidx12.174.3, i64 %351
  %352 = load float, float* %arrayidx14.175.3, align 4, !tbaa !3
  %mul.176.3 = fmul float %350, %352
  %add.177.3 = fadd float %add53.1.3, %mul.176.3
  %indvars.iv.next.178.3 = or i64 %indvars.iv.1.3, 1
  %arrayidx10.1.1.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.178.3
  %353 = load float, float* %arrayidx10.1.1.3, align 4, !tbaa !3
  %354 = mul nuw nsw i64 %indvars.iv.next.178.3, %0
  %arrayidx12.1.1.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.3376
  %arrayidx14.1.1.3 = getelementptr inbounds float, float* %arrayidx12.1.1.3, i64 %354
  %355 = load float, float* %arrayidx14.1.1.3, align 4, !tbaa !3
  %mul.1.1.3 = fmul float %353, %355
  %add.1.1.3 = fadd float %add.177.3, %mul.1.1.3
  %indvars.iv.next.1.1.3 = or i64 %indvars.iv.1.3, 2
  %arrayidx10.2.1.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.1.1.3
  %356 = load float, float* %arrayidx10.2.1.3, align 4, !tbaa !3
  %357 = mul nuw nsw i64 %indvars.iv.next.1.1.3, %0
  %arrayidx12.2.1.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.3376
  %arrayidx14.2.1.3 = getelementptr inbounds float, float* %arrayidx12.2.1.3, i64 %357
  %358 = load float, float* %arrayidx14.2.1.3, align 4, !tbaa !3
  %mul.2.1.3 = fmul float %356, %358
  %add.2.1.3 = fadd float %add.1.1.3, %mul.2.1.3
  %indvars.iv.next.2.1.3 = or i64 %indvars.iv.1.3, 3
  %arrayidx10.3.1.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.2.1.3
  %359 = load float, float* %arrayidx10.3.1.3, align 4, !tbaa !3
  %360 = mul nuw nsw i64 %indvars.iv.next.2.1.3, %0
  %arrayidx12.3.1.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.3376
  %arrayidx14.3.1.3 = getelementptr inbounds float, float* %arrayidx12.3.1.3, i64 %360
  %361 = load float, float* %arrayidx14.3.1.3, align 4, !tbaa !3
  %mul.3.1.3 = fmul float %359, %361
  %add.3.1.3 = fadd float %add.2.1.3, %mul.3.1.3
  %indvars.iv.next.3.1.3 = add nuw nsw i64 %indvars.iv.1.3, 4
  %niter.nsub.3.1.3 = add i32 %niter.1.3, -4
  %niter.ncmp.3.1.3.not = icmp eq i32 %niter.nsub.3.1.3, 0
  br i1 %niter.ncmp.3.1.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3.loopexit, label %for.body8.1.3, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3.loopexit: ; preds = %for.body8.1.3
  %add.3.1.3.lcssa = phi float [ %add.3.1.3, %for.body8.1.3 ]
  %indvars.iv.next.3.1.3.lcssa = phi i64 [ %indvars.iv.next.3.1.3, %for.body8.1.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.3375
  %add.lcssa.ph.1.3 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.3375 ], [ %add.3.1.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3.loopexit ]
  %indvars.iv.unr.1.3 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.3375 ], [ %indvars.iv.next.3.1.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3.loopexit ]
  %add53.unr.1.3 = phi float [ %arrayidx18.promoted.1.3, %for.cond5.for.cond.cleanup7_crit_edge.3375 ], [ %add.3.1.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3.loopexit ]
  %lcmp.mod.1.3.not = icmp eq i32 %xtraiter.1.3, 0
  br i1 %lcmp.mod.1.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.3, label %for.body8.epil.1.3.preheader

for.body8.epil.1.3.preheader:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3
  br label %for.body8.epil.1.3

for.body8.epil.1.3:                               ; preds = %for.body8.epil.1.3.preheader, %for.body8.epil.1.3
  %indvars.iv.epil.1.3 = phi i64 [ %indvars.iv.next.epil.1.3, %for.body8.epil.1.3 ], [ %indvars.iv.unr.1.3, %for.body8.epil.1.3.preheader ]
  %add53.epil.1.3 = phi float [ %add.epil.1.3, %for.body8.epil.1.3 ], [ %add53.unr.1.3, %for.body8.epil.1.3.preheader ]
  %epil.iter.1.3 = phi i32 [ %epil.iter.sub.1.3, %for.body8.epil.1.3 ], [ %xtraiter.1.3, %for.body8.epil.1.3.preheader ]
  %arrayidx10.epil.1.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.epil.1.3
  %362 = load float, float* %arrayidx10.epil.1.3, align 4, !tbaa !3
  %363 = mul nuw nsw i64 %indvars.iv.epil.1.3, %0
  %arrayidx12.epil.1.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.3376
  %arrayidx14.epil.1.3 = getelementptr inbounds float, float* %arrayidx12.epil.1.3, i64 %363
  %364 = load float, float* %arrayidx14.epil.1.3, align 4, !tbaa !3
  %mul.epil.1.3 = fmul float %362, %364
  %add.epil.1.3 = fadd float %add53.epil.1.3, %mul.epil.1.3
  %indvars.iv.next.epil.1.3 = add nuw nsw i64 %indvars.iv.epil.1.3, 1
  %epil.iter.sub.1.3 = add i32 %epil.iter.1.3, -1
  %epil.iter.cmp.1.3.not = icmp eq i32 %epil.iter.sub.1.3, 0
  br i1 %epil.iter.cmp.1.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.1.3.loopexit, label %for.body8.epil.1.3, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.1.3.loopexit: ; preds = %for.body8.epil.1.3
  %add.epil.1.3.lcssa = phi float [ %add.epil.1.3, %for.body8.epil.1.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.1.3

for.cond5.for.cond.cleanup7_crit_edge.1.3:        ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.3.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3
  %add.lcssa.1.3 = phi float [ %add.lcssa.ph.1.3, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.1.3 ], [ %add.epil.1.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.1.3.loopexit ]
  store float %add.lcssa.1.3, float* %arrayidx18.1.3, align 4, !tbaa !3
  %indvars.iv.next56.1.3 = or i64 %indvars.iv55.3, 2
  %arrayidx18.2.3 = getelementptr inbounds float, float* %arrayidx16.3, i64 %indvars.iv.next56.1.3
  %arrayidx18.promoted.2.3 = load float, float* %arrayidx18.2.3, align 4, !tbaa !3
  %xtraiter.2.3 = and i32 %n, 3
  %365 = icmp ult i32 %1, 3
  br i1 %365, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3, label %for.body8.lr.ph.new.2.3

for.body8.lr.ph.new.2.3:                          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.1.3
  %unroll_iter.2.3 = and i32 %n, -4
  br label %for.body8.2.3

for.body8.2.3:                                    ; preds = %for.body8.2.3, %for.body8.lr.ph.new.2.3
  %indvars.iv.2.3 = phi i64 [ 0, %for.body8.lr.ph.new.2.3 ], [ %indvars.iv.next.3.2.3, %for.body8.2.3 ]
  %add53.2.3 = phi float [ %arrayidx18.promoted.2.3, %for.body8.lr.ph.new.2.3 ], [ %add.3.2.3, %for.body8.2.3 ]
  %niter.2.3 = phi i32 [ %unroll_iter.2.3, %for.body8.lr.ph.new.2.3 ], [ %niter.nsub.3.2.3, %for.body8.2.3 ]
  %arrayidx10.280.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.2.3
  %366 = load float, float* %arrayidx10.280.3, align 4, !tbaa !3
  %367 = mul nuw nsw i64 %indvars.iv.2.3, %0
  %arrayidx12.281.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.3
  %arrayidx14.282.3 = getelementptr inbounds float, float* %arrayidx12.281.3, i64 %367
  %368 = load float, float* %arrayidx14.282.3, align 4, !tbaa !3
  %mul.283.3 = fmul float %366, %368
  %add.284.3 = fadd float %add53.2.3, %mul.283.3
  %indvars.iv.next.285.3 = or i64 %indvars.iv.2.3, 1
  %arrayidx10.1.2.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.285.3
  %369 = load float, float* %arrayidx10.1.2.3, align 4, !tbaa !3
  %370 = mul nuw nsw i64 %indvars.iv.next.285.3, %0
  %arrayidx12.1.2.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.3
  %arrayidx14.1.2.3 = getelementptr inbounds float, float* %arrayidx12.1.2.3, i64 %370
  %371 = load float, float* %arrayidx14.1.2.3, align 4, !tbaa !3
  %mul.1.2.3 = fmul float %369, %371
  %add.1.2.3 = fadd float %add.284.3, %mul.1.2.3
  %indvars.iv.next.1.2.3 = or i64 %indvars.iv.2.3, 2
  %arrayidx10.2.2.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.1.2.3
  %372 = load float, float* %arrayidx10.2.2.3, align 4, !tbaa !3
  %373 = mul nuw nsw i64 %indvars.iv.next.1.2.3, %0
  %arrayidx12.2.2.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.3
  %arrayidx14.2.2.3 = getelementptr inbounds float, float* %arrayidx12.2.2.3, i64 %373
  %374 = load float, float* %arrayidx14.2.2.3, align 4, !tbaa !3
  %mul.2.2.3 = fmul float %372, %374
  %add.2.2.3 = fadd float %add.1.2.3, %mul.2.2.3
  %indvars.iv.next.2.2.3 = or i64 %indvars.iv.2.3, 3
  %arrayidx10.3.2.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.2.2.3
  %375 = load float, float* %arrayidx10.3.2.3, align 4, !tbaa !3
  %376 = mul nuw nsw i64 %indvars.iv.next.2.2.3, %0
  %arrayidx12.3.2.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.3
  %arrayidx14.3.2.3 = getelementptr inbounds float, float* %arrayidx12.3.2.3, i64 %376
  %377 = load float, float* %arrayidx14.3.2.3, align 4, !tbaa !3
  %mul.3.2.3 = fmul float %375, %377
  %add.3.2.3 = fadd float %add.2.2.3, %mul.3.2.3
  %indvars.iv.next.3.2.3 = add nuw nsw i64 %indvars.iv.2.3, 4
  %niter.nsub.3.2.3 = add i32 %niter.2.3, -4
  %niter.ncmp.3.2.3.not = icmp eq i32 %niter.nsub.3.2.3, 0
  br i1 %niter.ncmp.3.2.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3.loopexit, label %for.body8.2.3, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3.loopexit: ; preds = %for.body8.2.3
  %add.3.2.3.lcssa = phi float [ %add.3.2.3, %for.body8.2.3 ]
  %indvars.iv.next.3.2.3.lcssa = phi i64 [ %indvars.iv.next.3.2.3, %for.body8.2.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.1.3
  %add.lcssa.ph.2.3 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.1.3 ], [ %add.3.2.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3.loopexit ]
  %indvars.iv.unr.2.3 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.1.3 ], [ %indvars.iv.next.3.2.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3.loopexit ]
  %add53.unr.2.3 = phi float [ %arrayidx18.promoted.2.3, %for.cond5.for.cond.cleanup7_crit_edge.1.3 ], [ %add.3.2.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3.loopexit ]
  %lcmp.mod.2.3.not = icmp eq i32 %xtraiter.2.3, 0
  br i1 %lcmp.mod.2.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.2.3, label %for.body8.epil.2.3.preheader

for.body8.epil.2.3.preheader:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3
  br label %for.body8.epil.2.3

for.body8.epil.2.3:                               ; preds = %for.body8.epil.2.3.preheader, %for.body8.epil.2.3
  %indvars.iv.epil.2.3 = phi i64 [ %indvars.iv.next.epil.2.3, %for.body8.epil.2.3 ], [ %indvars.iv.unr.2.3, %for.body8.epil.2.3.preheader ]
  %add53.epil.2.3 = phi float [ %add.epil.2.3, %for.body8.epil.2.3 ], [ %add53.unr.2.3, %for.body8.epil.2.3.preheader ]
  %epil.iter.2.3 = phi i32 [ %epil.iter.sub.2.3, %for.body8.epil.2.3 ], [ %xtraiter.2.3, %for.body8.epil.2.3.preheader ]
  %arrayidx10.epil.2.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.epil.2.3
  %378 = load float, float* %arrayidx10.epil.2.3, align 4, !tbaa !3
  %379 = mul nuw nsw i64 %indvars.iv.epil.2.3, %0
  %arrayidx12.epil.2.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.1.3
  %arrayidx14.epil.2.3 = getelementptr inbounds float, float* %arrayidx12.epil.2.3, i64 %379
  %380 = load float, float* %arrayidx14.epil.2.3, align 4, !tbaa !3
  %mul.epil.2.3 = fmul float %378, %380
  %add.epil.2.3 = fadd float %add53.epil.2.3, %mul.epil.2.3
  %indvars.iv.next.epil.2.3 = add nuw nsw i64 %indvars.iv.epil.2.3, 1
  %epil.iter.sub.2.3 = add i32 %epil.iter.2.3, -1
  %epil.iter.cmp.2.3.not = icmp eq i32 %epil.iter.sub.2.3, 0
  br i1 %epil.iter.cmp.2.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.2.3.loopexit, label %for.body8.epil.2.3, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.2.3.loopexit: ; preds = %for.body8.epil.2.3
  %add.epil.2.3.lcssa = phi float [ %add.epil.2.3, %for.body8.epil.2.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.2.3

for.cond5.for.cond.cleanup7_crit_edge.2.3:        ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2.3.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3
  %add.lcssa.2.3 = phi float [ %add.lcssa.ph.2.3, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.2.3 ], [ %add.epil.2.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.2.3.loopexit ]
  store float %add.lcssa.2.3, float* %arrayidx18.2.3, align 4, !tbaa !3
  %indvars.iv.next56.2.3 = or i64 %indvars.iv55.3, 3
  %arrayidx18.3.3 = getelementptr inbounds float, float* %arrayidx16.3, i64 %indvars.iv.next56.2.3
  %arrayidx18.promoted.3.3 = load float, float* %arrayidx18.3.3, align 4, !tbaa !3
  %xtraiter.3.3 = and i32 %n, 3
  %381 = icmp ult i32 %1, 3
  br i1 %381, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3, label %for.body8.lr.ph.new.3.3

for.body8.lr.ph.new.3.3:                          ; preds = %for.cond5.for.cond.cleanup7_crit_edge.2.3
  %unroll_iter.3.3 = and i32 %n, -4
  br label %for.body8.3.3

for.body8.3.3:                                    ; preds = %for.body8.3.3, %for.body8.lr.ph.new.3.3
  %indvars.iv.3.3 = phi i64 [ 0, %for.body8.lr.ph.new.3.3 ], [ %indvars.iv.next.3.3.3, %for.body8.3.3 ]
  %add53.3.3 = phi float [ %arrayidx18.promoted.3.3, %for.body8.lr.ph.new.3.3 ], [ %add.3.3.3, %for.body8.3.3 ]
  %niter.3.3 = phi i32 [ %unroll_iter.3.3, %for.body8.lr.ph.new.3.3 ], [ %niter.nsub.3.3.3, %for.body8.3.3 ]
  %arrayidx10.387.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.3.3
  %382 = load float, float* %arrayidx10.387.3, align 4, !tbaa !3
  %383 = mul nuw nsw i64 %indvars.iv.3.3, %0
  %arrayidx12.388.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.3
  %arrayidx14.389.3 = getelementptr inbounds float, float* %arrayidx12.388.3, i64 %383
  %384 = load float, float* %arrayidx14.389.3, align 4, !tbaa !3
  %mul.390.3 = fmul float %382, %384
  %add.391.3 = fadd float %add53.3.3, %mul.390.3
  %indvars.iv.next.392.3 = or i64 %indvars.iv.3.3, 1
  %arrayidx10.1.3.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.392.3
  %385 = load float, float* %arrayidx10.1.3.3, align 4, !tbaa !3
  %386 = mul nuw nsw i64 %indvars.iv.next.392.3, %0
  %arrayidx12.1.3.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.3
  %arrayidx14.1.3.3 = getelementptr inbounds float, float* %arrayidx12.1.3.3, i64 %386
  %387 = load float, float* %arrayidx14.1.3.3, align 4, !tbaa !3
  %mul.1.3.3 = fmul float %385, %387
  %add.1.3.3 = fadd float %add.391.3, %mul.1.3.3
  %indvars.iv.next.1.3.3 = or i64 %indvars.iv.3.3, 2
  %arrayidx10.2.3.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.1.3.3
  %388 = load float, float* %arrayidx10.2.3.3, align 4, !tbaa !3
  %389 = mul nuw nsw i64 %indvars.iv.next.1.3.3, %0
  %arrayidx12.2.3.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.3
  %arrayidx14.2.3.3 = getelementptr inbounds float, float* %arrayidx12.2.3.3, i64 %389
  %390 = load float, float* %arrayidx14.2.3.3, align 4, !tbaa !3
  %mul.2.3.3 = fmul float %388, %390
  %add.2.3.3 = fadd float %add.1.3.3, %mul.2.3.3
  %indvars.iv.next.2.3.3 = or i64 %indvars.iv.3.3, 3
  %arrayidx10.3.3.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.2.3.3
  %391 = load float, float* %arrayidx10.3.3.3, align 4, !tbaa !3
  %392 = mul nuw nsw i64 %indvars.iv.next.2.3.3, %0
  %arrayidx12.3.3.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.3
  %arrayidx14.3.3.3 = getelementptr inbounds float, float* %arrayidx12.3.3.3, i64 %392
  %393 = load float, float* %arrayidx14.3.3.3, align 4, !tbaa !3
  %mul.3.3.3 = fmul float %391, %393
  %add.3.3.3 = fadd float %add.2.3.3, %mul.3.3.3
  %indvars.iv.next.3.3.3 = add nuw nsw i64 %indvars.iv.3.3, 4
  %niter.nsub.3.3.3 = add i32 %niter.3.3, -4
  %niter.ncmp.3.3.3.not = icmp eq i32 %niter.nsub.3.3.3, 0
  br i1 %niter.ncmp.3.3.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3.loopexit, label %for.body8.3.3, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3.loopexit: ; preds = %for.body8.3.3
  %add.3.3.3.lcssa = phi float [ %add.3.3.3, %for.body8.3.3 ]
  %indvars.iv.next.3.3.3.lcssa = phi i64 [ %indvars.iv.next.3.3.3, %for.body8.3.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.2.3
  %add.lcssa.ph.3.3 = phi float [ undef, %for.cond5.for.cond.cleanup7_crit_edge.2.3 ], [ %add.3.3.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3.loopexit ]
  %indvars.iv.unr.3.3 = phi i64 [ 0, %for.cond5.for.cond.cleanup7_crit_edge.2.3 ], [ %indvars.iv.next.3.3.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3.loopexit ]
  %add53.unr.3.3 = phi float [ %arrayidx18.promoted.3.3, %for.cond5.for.cond.cleanup7_crit_edge.2.3 ], [ %add.3.3.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3.loopexit ]
  %lcmp.mod.3.3.not = icmp eq i32 %xtraiter.3.3, 0
  br i1 %lcmp.mod.3.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.3.3, label %for.body8.epil.3.3.preheader

for.body8.epil.3.3.preheader:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3
  br label %for.body8.epil.3.3

for.body8.epil.3.3:                               ; preds = %for.body8.epil.3.3.preheader, %for.body8.epil.3.3
  %indvars.iv.epil.3.3 = phi i64 [ %indvars.iv.next.epil.3.3, %for.body8.epil.3.3 ], [ %indvars.iv.unr.3.3, %for.body8.epil.3.3.preheader ]
  %add53.epil.3.3 = phi float [ %add.epil.3.3, %for.body8.epil.3.3 ], [ %add53.unr.3.3, %for.body8.epil.3.3.preheader ]
  %epil.iter.3.3 = phi i32 [ %epil.iter.sub.3.3, %for.body8.epil.3.3 ], [ %xtraiter.3.3, %for.body8.epil.3.3.preheader ]
  %arrayidx10.epil.3.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.epil.3.3
  %394 = load float, float* %arrayidx10.epil.3.3, align 4, !tbaa !3
  %395 = mul nuw nsw i64 %indvars.iv.epil.3.3, %0
  %arrayidx12.epil.3.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv.next56.2.3
  %arrayidx14.epil.3.3 = getelementptr inbounds float, float* %arrayidx12.epil.3.3, i64 %395
  %396 = load float, float* %arrayidx14.epil.3.3, align 4, !tbaa !3
  %mul.epil.3.3 = fmul float %394, %396
  %add.epil.3.3 = fadd float %add53.epil.3.3, %mul.epil.3.3
  %indvars.iv.next.epil.3.3 = add nuw nsw i64 %indvars.iv.epil.3.3, 1
  %epil.iter.sub.3.3 = add i32 %epil.iter.3.3, -1
  %epil.iter.cmp.3.3.not = icmp eq i32 %epil.iter.sub.3.3, 0
  br i1 %epil.iter.cmp.3.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.3.3.loopexit, label %for.body8.epil.3.3, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.3.3.loopexit: ; preds = %for.body8.epil.3.3
  %add.epil.3.3.lcssa = phi float [ %add.epil.3.3, %for.body8.epil.3.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.3.3

for.cond5.for.cond.cleanup7_crit_edge.3.3:        ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.3.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3
  %add.lcssa.3.3 = phi float [ %add.lcssa.ph.3.3, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.3.3 ], [ %add.epil.3.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.3.3.loopexit ]
  store float %add.lcssa.3.3, float* %arrayidx18.3.3, align 4, !tbaa !3
  %indvars.iv.next56.3.3 = add nuw nsw i64 %indvars.iv55.3, 4
  %niter72.nsub.3.3 = add i32 %niter72.3, -4
  %niter72.ncmp.3.3.not = icmp eq i32 %niter72.nsub.3.3, 0
  br i1 %niter72.ncmp.3.3.not, label %for.cond.cleanup3.loopexit.unr-lcssa.3.loopexit, label %for.cond5.preheader.3, !llvm.loop !11

for.cond.cleanup3.loopexit.unr-lcssa.3.loopexit:  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.3.3
  %indvars.iv.next56.3.3.lcssa = phi i64 [ %indvars.iv.next56.3.3, %for.cond5.for.cond.cleanup7_crit_edge.3.3 ]
  br label %for.cond.cleanup3.loopexit.unr-lcssa.3

for.cond.cleanup3.loopexit.unr-lcssa.3:           ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.3.loopexit, %for.cond5.preheader.lr.ph.3
  %indvars.iv55.unr.3 = phi i64 [ 0, %for.cond5.preheader.lr.ph.3 ], [ %indvars.iv.next56.3.3.lcssa, %for.cond.cleanup3.loopexit.unr-lcssa.3.loopexit ]
  %lcmp.mod70.3.not = icmp eq i32 %xtraiter58.3, 0
  br i1 %lcmp.mod70.3.not, label %for.cond.cleanup3.3, label %for.cond5.preheader.epil.3.preheader

for.cond5.preheader.epil.3.preheader:             ; preds = %for.cond.cleanup3.loopexit.unr-lcssa.3
  br label %for.cond5.preheader.epil.3

for.cond5.preheader.epil.3:                       ; preds = %for.cond5.preheader.epil.3.preheader, %for.cond5.for.cond.cleanup7_crit_edge.epil.3
  %indvars.iv55.epil.3 = phi i64 [ %indvars.iv.next56.epil.3, %for.cond5.for.cond.cleanup7_crit_edge.epil.3 ], [ %indvars.iv55.unr.3, %for.cond5.preheader.epil.3.preheader ]
  %epil.iter69.3 = phi i32 [ %epil.iter69.sub.3, %for.cond5.for.cond.cleanup7_crit_edge.epil.3 ], [ %xtraiter58.3, %for.cond5.preheader.epil.3.preheader ]
  %arrayidx18.epil.3 = getelementptr inbounds float, float* %arrayidx16.3, i64 %indvars.iv55.epil.3
  %arrayidx18.promoted.epil.3 = load float, float* %arrayidx18.epil.3, align 4, !tbaa !3
  %xtraiter.epil.3 = and i32 %n, 3
  %397 = icmp ult i32 %1, 3
  br i1 %397, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3, label %for.body8.lr.ph.new.epil.3

for.body8.lr.ph.new.epil.3:                       ; preds = %for.cond5.preheader.epil.3
  %unroll_iter.epil.3 = and i32 %n, -4
  br label %for.body8.epil59.3

for.body8.epil59.3:                               ; preds = %for.body8.epil59.3, %for.body8.lr.ph.new.epil.3
  %indvars.iv.epil60.3 = phi i64 [ 0, %for.body8.lr.ph.new.epil.3 ], [ %indvars.iv.next.3.epil.3, %for.body8.epil59.3 ]
  %add53.epil61.3 = phi float [ %arrayidx18.promoted.epil.3, %for.body8.lr.ph.new.epil.3 ], [ %add.3.epil.3, %for.body8.epil59.3 ]
  %niter.epil.3 = phi i32 [ %unroll_iter.epil.3, %for.body8.lr.ph.new.epil.3 ], [ %niter.nsub.3.epil.3, %for.body8.epil59.3 ]
  %arrayidx10.epil62.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.epil60.3
  %398 = load float, float* %arrayidx10.epil62.3, align 4, !tbaa !3
  %399 = mul nuw nsw i64 %indvars.iv.epil60.3, %0
  %arrayidx12.epil63.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.3
  %arrayidx14.epil64.3 = getelementptr inbounds float, float* %arrayidx12.epil63.3, i64 %399
  %400 = load float, float* %arrayidx14.epil64.3, align 4, !tbaa !3
  %mul.epil65.3 = fmul float %398, %400
  %add.epil66.3 = fadd float %add53.epil61.3, %mul.epil65.3
  %indvars.iv.next.epil67.3 = or i64 %indvars.iv.epil60.3, 1
  %arrayidx10.1.epil.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.epil67.3
  %401 = load float, float* %arrayidx10.1.epil.3, align 4, !tbaa !3
  %402 = mul nuw nsw i64 %indvars.iv.next.epil67.3, %0
  %arrayidx12.1.epil.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.3
  %arrayidx14.1.epil.3 = getelementptr inbounds float, float* %arrayidx12.1.epil.3, i64 %402
  %403 = load float, float* %arrayidx14.1.epil.3, align 4, !tbaa !3
  %mul.1.epil.3 = fmul float %401, %403
  %add.1.epil.3 = fadd float %add.epil66.3, %mul.1.epil.3
  %indvars.iv.next.1.epil.3 = or i64 %indvars.iv.epil60.3, 2
  %arrayidx10.2.epil.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.1.epil.3
  %404 = load float, float* %arrayidx10.2.epil.3, align 4, !tbaa !3
  %405 = mul nuw nsw i64 %indvars.iv.next.1.epil.3, %0
  %arrayidx12.2.epil.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.3
  %arrayidx14.2.epil.3 = getelementptr inbounds float, float* %arrayidx12.2.epil.3, i64 %405
  %406 = load float, float* %arrayidx14.2.epil.3, align 4, !tbaa !3
  %mul.2.epil.3 = fmul float %404, %406
  %add.2.epil.3 = fadd float %add.1.epil.3, %mul.2.epil.3
  %indvars.iv.next.2.epil.3 = or i64 %indvars.iv.epil60.3, 3
  %arrayidx10.3.epil.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.next.2.epil.3
  %407 = load float, float* %arrayidx10.3.epil.3, align 4, !tbaa !3
  %408 = mul nuw nsw i64 %indvars.iv.next.2.epil.3, %0
  %arrayidx12.3.epil.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.3
  %arrayidx14.3.epil.3 = getelementptr inbounds float, float* %arrayidx12.3.epil.3, i64 %408
  %409 = load float, float* %arrayidx14.3.epil.3, align 4, !tbaa !3
  %mul.3.epil.3 = fmul float %407, %409
  %add.3.epil.3 = fadd float %add.2.epil.3, %mul.3.epil.3
  %indvars.iv.next.3.epil.3 = add nuw nsw i64 %indvars.iv.epil60.3, 4
  %niter.nsub.3.epil.3 = add i32 %niter.epil.3, -4
  %niter.ncmp.3.epil.3.not = icmp eq i32 %niter.nsub.3.epil.3, 0
  br i1 %niter.ncmp.3.epil.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3.loopexit, label %for.body8.epil59.3, !llvm.loop !7

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3.loopexit: ; preds = %for.body8.epil59.3
  %add.3.epil.3.lcssa = phi float [ %add.3.epil.3, %for.body8.epil59.3 ]
  %indvars.iv.next.3.epil.3.lcssa = phi i64 [ %indvars.iv.next.3.epil.3, %for.body8.epil59.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3

for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3: ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3.loopexit, %for.cond5.preheader.epil.3
  %add.lcssa.ph.epil.3 = phi float [ undef, %for.cond5.preheader.epil.3 ], [ %add.3.epil.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3.loopexit ]
  %indvars.iv.unr.epil.3 = phi i64 [ 0, %for.cond5.preheader.epil.3 ], [ %indvars.iv.next.3.epil.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3.loopexit ]
  %add53.unr.epil.3 = phi float [ %arrayidx18.promoted.epil.3, %for.cond5.preheader.epil.3 ], [ %add.3.epil.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3.loopexit ]
  %lcmp.mod.epil.3.not = icmp eq i32 %xtraiter.epil.3, 0
  br i1 %lcmp.mod.epil.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.3, label %for.body8.epil.epil.3.preheader

for.body8.epil.epil.3.preheader:                  ; preds = %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3
  br label %for.body8.epil.epil.3

for.body8.epil.epil.3:                            ; preds = %for.body8.epil.epil.3.preheader, %for.body8.epil.epil.3
  %indvars.iv.epil.epil.3 = phi i64 [ %indvars.iv.next.epil.epil.3, %for.body8.epil.epil.3 ], [ %indvars.iv.unr.epil.3, %for.body8.epil.epil.3.preheader ]
  %add53.epil.epil.3 = phi float [ %add.epil.epil.3, %for.body8.epil.epil.3 ], [ %add53.unr.epil.3, %for.body8.epil.epil.3.preheader ]
  %epil.iter.epil.3 = phi i32 [ %epil.iter.sub.epil.3, %for.body8.epil.epil.3 ], [ %xtraiter.epil.3, %for.body8.epil.epil.3.preheader ]
  %arrayidx10.epil.epil.3 = getelementptr inbounds float, float* %arrayidx.3, i64 %indvars.iv.epil.epil.3
  %410 = load float, float* %arrayidx10.epil.epil.3, align 4, !tbaa !3
  %411 = mul nuw nsw i64 %indvars.iv.epil.epil.3, %0
  %arrayidx12.epil.epil.3 = getelementptr inbounds float, float* %b, i64 %indvars.iv55.epil.3
  %arrayidx14.epil.epil.3 = getelementptr inbounds float, float* %arrayidx12.epil.epil.3, i64 %411
  %412 = load float, float* %arrayidx14.epil.epil.3, align 4, !tbaa !3
  %mul.epil.epil.3 = fmul float %410, %412
  %add.epil.epil.3 = fadd float %add53.epil.epil.3, %mul.epil.epil.3
  %indvars.iv.next.epil.epil.3 = add nuw nsw i64 %indvars.iv.epil.epil.3, 1
  %epil.iter.sub.epil.3 = add i32 %epil.iter.epil.3, -1
  %epil.iter.cmp.epil.3.not = icmp eq i32 %epil.iter.sub.epil.3, 0
  br i1 %epil.iter.cmp.epil.3.not, label %for.cond5.for.cond.cleanup7_crit_edge.epil.3.loopexit, label %for.body8.epil.epil.3, !llvm.loop !10

for.cond5.for.cond.cleanup7_crit_edge.epil.3.loopexit: ; preds = %for.body8.epil.epil.3
  %add.epil.epil.3.lcssa = phi float [ %add.epil.epil.3, %for.body8.epil.epil.3 ]
  br label %for.cond5.for.cond.cleanup7_crit_edge.epil.3

for.cond5.for.cond.cleanup7_crit_edge.epil.3:     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil.3.loopexit, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3
  %add.lcssa.epil.3 = phi float [ %add.lcssa.ph.epil.3, %for.cond5.for.cond.cleanup7_crit_edge.unr-lcssa.epil.3 ], [ %add.epil.epil.3.lcssa, %for.cond5.for.cond.cleanup7_crit_edge.epil.3.loopexit ]
  store float %add.lcssa.epil.3, float* %arrayidx18.epil.3, align 4, !tbaa !3
  %indvars.iv.next56.epil.3 = add nuw nsw i64 %indvars.iv55.epil.3, 1
  %epil.iter69.sub.3 = add i32 %epil.iter69.3, -1
  %epil.iter69.cmp.3.not = icmp eq i32 %epil.iter69.sub.3, 0
  br i1 %epil.iter69.cmp.3.not, label %for.cond.cleanup3.3.loopexit, label %for.cond5.preheader.epil.3, !llvm.loop !12

for.cond.cleanup3.3.loopexit:                     ; preds = %for.cond5.for.cond.cleanup7_crit_edge.epil.3
  br label %for.cond.cleanup3.3

for.cond.cleanup3.3:                              ; preds = %for.cond.cleanup3.3.loopexit, %for.cond.cleanup3.loopexit.unr-lcssa.3
  %indvars.iv.next95.3 = add nuw nsw i64 %indvars.iv94, 4
  %niter171.nsub.3 = add i32 %niter171, -4
  %niter171.ncmp.3.not = icmp eq i32 %niter171.nsub.3, 0
  br i1 %niter171.ncmp.3.not, label %for.cond.cleanup.loopexit.unr-lcssa.loopexit, label %for.cond1.preheader, !llvm.loop !14
}

attributes #0 = { nofree norecurse nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"float", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = distinct !{!7, !8, !9}
!8 = !{!"llvm.loop.mustprogress"}
!9 = !{!"llvm.loop.unroll.disable"}
!10 = distinct !{!10, !9}
!11 = distinct !{!11, !8, !9}
!12 = distinct !{!12, !9}
!13 = distinct !{!13, !9}
!14 = distinct !{!14, !8, !9}
