; RUN: %opt -gslp %s -o - -S | FileCheck %s
target triple = "x86_64-apple-macosx10.15.0"

; CHECK: entry:
; CHECK:   %tobool = icmp ne i32 %x, 0
; CHECK:   br i1 %tobool, label %if.then, label %if.else

; CHECK: if.then:
; CHECK-NEXT:   %arrayidx = getelementptr inbounds i32, i32* %a, i64 0
; CHECK-NEXT:   %0 = bitcast i32* %arrayidx to <2 x i32>*
; CHECK-NEXT:   %1 = load <2 x i32>, <2 x i32>* %0, align 4, !tbaa !3
; CHECK-NEXT:   br label %if.end

; CHECK: if.else:
; CHECK-NEXT:   %arrayidx2 = getelementptr inbounds i32, i32* %b, i64 0
; CHECK-NEXT:   %2 = bitcast i32* %arrayidx2 to <2 x i32>*
; CHECK-NEXT:   %3 = load <2 x i32>, <2 x i32>* %2, align 4, !tbaa !3
; CHECK-NEXT:   br label %if.end

; CHECK: if.end:
; CHECK-NEXT:   %4 = phi <2 x i32> [ %1, %if.then ], [ %3, %if.else ]
; CHECK-NEXT:   %arrayidx4 = getelementptr inbounds i32, i32* %c, i64 0
; CHECK-NEXT:   %5 = bitcast i32* %arrayidx4 to <2 x i32>*
; CHECK-NEXT:   store <2 x i32> %4, <2 x i32>* %5, align 4, !tbaa !3
; CHECK-NEXT:   ret void


; Function Attrs: nounwind ssp uwtable
define dso_local void @foo(i32 %x, i32* %a, i32* %b, i32* %c) #0 {
entry:
  %tobool = icmp ne i32 %x, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %arrayidx = getelementptr inbounds i32, i32* %a, i64 0
  %0 = load i32, i32* %arrayidx, align 4, !tbaa !3
  %arrayidx1 = getelementptr inbounds i32, i32* %a, i64 1
  %1 = load i32, i32* %arrayidx1, align 4, !tbaa !3
  br label %if.end

if.else:                                          ; preds = %entry
  %arrayidx2 = getelementptr inbounds i32, i32* %b, i64 0
  %2 = load i32, i32* %arrayidx2, align 4, !tbaa !3
  %arrayidx3 = getelementptr inbounds i32, i32* %b, i64 1
  %3 = load i32, i32* %arrayidx3, align 4, !tbaa !3
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %p.0 = phi i32 [ %0, %if.then ], [ %2, %if.else ]
  %q.0 = phi i32 [ %1, %if.then ], [ %3, %if.else ]
  %arrayidx4 = getelementptr inbounds i32, i32* %c, i64 0
  store i32 %p.0, i32* %arrayidx4, align 4, !tbaa !3
  %arrayidx5 = getelementptr inbounds i32, i32* %c, i64 1
  store i32 %q.0, i32* %arrayidx5, align 4, !tbaa !3
  ret void
}

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: argmemonly nofree nosync nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

attributes #0 = { nounwind ssp uwtable "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nofree nosync nounwind willreturn }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 12.0.1 (https://github.com/llvm/llvm-project.git 328a6ec955327c6d56b6bc3478c723dd3cd468ef)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
