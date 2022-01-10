; RUN: %opt -gslp %s -o /dev/null
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.15.0"

define dso_local void @_ZN10btSoftBody16setVolumeDensityEf() local_unnamed_addr align 2 {
for.cond2.preheader.lr.ph.new:
  %unroll_iter = and i32 undef, -4
  br label %for.cond2.preheader

for.cond2.preheader:                              ; preds = %for.cond2.preheader, %for.cond2.preheader.lr.ph.new
  %add.lcssa18 = phi float [ undef, %for.cond2.preheader.lr.ph.new ], [ %add.3.3, %for.cond2.preheader ]
  %niter = phi i32 [ %unroll_iter, %for.cond2.preheader.lr.ph.new ], [ %niter.nsub.3, %for.cond2.preheader ]
  %add = fadd float undef, %add.lcssa18
  %add.1 = fadd float undef, %add
  %add.2 = fadd float undef, %add.1
  %add.3 = fadd float undef, %add.2
  %add.120 = fadd float undef, %add.3
  %add.1.1 = fadd float undef, %add.120
  %add.2.1 = fadd float undef, %add.1.1
  %add.3.1 = fadd float undef, %add.2.1
  %add.221 = fadd float undef, %add.3.1
  %add.1.2 = fadd float undef, %add.221
  %add.2.2 = fadd float undef, %add.1.2
  %add.3.2 = fadd float undef, %add.2.2
  %add.322 = fadd float undef, %add.3.2
  %add.1.3 = fadd float undef, %add.322
  %add.2.3 = fadd float undef, %add.1.3
  %add.3.3 = fadd float undef, %add.2.3
  %niter.nsub.3 = add i32 %niter, -4
  %niter.ncmp.3 = icmp eq i32 %niter.nsub.3, 0
  br i1 %niter.ncmp.3, label %for.cond.for.cond.cleanup_crit_edge.unr-lcssa.loopexit, label %for.cond2.preheader, !llvm.loop !0

for.cond.for.cond.cleanup_crit_edge.unr-lcssa.loopexit: ; preds = %for.cond2.preheader
  ret void
}

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.mustprogress"}
