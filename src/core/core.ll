define i1 @not-bool(i1) {
entry:
  %1 = xor i1 %0, true
  ret i1 %1
}

define i1 @and-bool(i1, i1) {
entry:
  %r = add i1 %0, %1
  ret i1 %r
}

define i1 @or-bool(i1, i1) {
entry:
  %r = or i1 %0, %1
  ret i1 %r
}

; int64

define i1 @eq-int64(i64, i64) {
entry:
  %r = icmp eq i64 %0, %1
  ret i1 %r
}

define i1 @neq-int64(i64, i64) {
entry:
  %r = icmp ne i64 %0, %1
  ret i1 %r
}

define i1 @gt-int64(i64, i64) {
entry:
  %r = icmp sgt i64 %0, %1
  ret i1 %r
}

define i1 @gteq-int64(i64, i64) {
entry:
  %r = icmp sge i64 %0, %1
  ret i1 %r
}

define i1 @lt-int64(i64, i64) {
entry:
  %r = icmp slt i64 %0, %1
  ret i1 %r
}

define i1 @lteq-int64(i64, i64) {
entry:
  %r = icmp sle i64 %0, %1
  ret i1 %r
}

define i64 @neg-int64(i64) {
entry:
  %1 = sub i64 0, %0
  ret i64 %1
}

define i64 @add-int64(i64, i64) {
entry:
  %r = add i64 %0, %1
  ret i64 %r
}

define i64 @sub-int64(i64, i64) {
entry:
  %r = sub i64 %0, %1
  ret i64 %r
}

define i64 @mul-int64(i64, i64) {
entry:
  %r = mul i64 %0, %1
  ret i64 %r
}

define i64 @div-int64(i64, i64) {
entry:
  %r = sdiv i64 %0, %1
  ret i64 %r
}

define i64 @shl-int64(i64, i64) {
entry:
  %r = shl i64 %0, %1
  ret i64 %r
}

define i64 @shr-int64(i64, i64) {
entry:
  %r = ashr i64 %0, %1
  ret i64 %r
}

; int32

define i1 @eq-int32(i32, i32) {
entry:
  %r = icmp eq i32 %0, %1
  ret i1 %r
}

define i1 @neq-int32(i32, i32) {
entry:
  %r = icmp ne i32 %0, %1
  ret i1 %r
}

define i1 @gt-int32(i32, i32) {
entry:
  %r = icmp sgt i32 %0, %1
  ret i1 %r
}

define i1 @gteq-int32(i32, i32) {
entry:
  %r = icmp sge i32 %0, %1
  ret i1 %r
}

define i1 @lt-int32(i32, i32) {
entry:
  %r = icmp slt i32 %0, %1
  ret i1 %r
}

define i1 @lteq-int32(i32, i32) {
entry:
  %r = icmp sle i32 %0, %1
  ret i1 %r
}

define i32 @neg-int32(i32) {
entry:
  %1 = sub i32 0, %0
  ret i32 %1
}

define i32 @add-int32(i32, i32) {
entry:
  %r = add i32 %0, %1
  ret i32 %r
}

define i32 @sub-int32(i32, i32) {
entry:
  %r = sub i32 %0, %1
  ret i32 %r
}

define i32 @mul-int32(i32, i32) {
entry:
  %r = mul i32 %0, %1
  ret i32 %r
}

define i32 @div-int32(i32, i32) {
entry:
  %r = sdiv i32 %0, %1
  ret i32 %r
}

define i32 @shl-int32(i32, i32) {
entry:
  %r = shl i32 %0, %1
  ret i32 %r
}

define i32 @shr-int32(i32, i32) {
entry:
  %r = ashr i32 %0, %1
  ret i32 %r
}

; int16

define i1 @eq-int16(i16, i16) {
entry:
  %r = icmp eq i16 %0, %1
  ret i1 %r
}

define i1 @neq-int16(i16, i16) {
entry:
  %r = icmp ne i16 %0, %1
  ret i1 %r
}

define i1 @gt-int16(i16, i16) {
entry:
  %r = icmp sgt i16 %0, %1
  ret i1 %r
}

define i1 @gteq-int16(i16, i16) {
entry:
  %r = icmp sge i16 %0, %1
  ret i1 %r
}

define i1 @lt-int16(i16, i16) {
entry:
  %r = icmp slt i16 %0, %1
  ret i1 %r
}

define i1 @lteq-int16(i16, i16) {
entry:
  %r = icmp sle i16 %0, %1
  ret i1 %r
}

define i16 @neg-int16(i16) {
entry:
  %1 = sub i16 0, %0
  ret i16 %1
}

define i16 @add-int16(i16, i16) {
entry:
  %r = add i16 %0, %1
  ret i16 %r
}

define i16 @sub-int16(i16, i16) {
entry:
  %r = sub i16 %0, %1
  ret i16 %r
}

define i16 @mul-int16(i16, i16) {
entry:
  %r = mul i16 %0, %1
  ret i16 %r
}

define i16 @div-int16(i16, i16) {
entry:
  %r = sdiv i16 %0, %1
  ret i16 %r
}

define i16 @shl-int16(i16, i16) {
entry:
  %r = shl i16 %0, %1
  ret i16 %r
}

define i16 @shr-int16(i16, i16) {
entry:
  %r = ashr i16 %0, %1
  ret i16 %r
}

; int8

define i1 @eq-int8(i8, i8) {
entry:
  %r = icmp eq i8 %0, %1
  ret i1 %r
}

define i1 @neq-int8(i8, i8) {
entry:
  %r = icmp ne i8 %0, %1
  ret i1 %r
}

define i1 @gt-int8(i8, i8) {
entry:
  %r = icmp sgt i8 %0, %1
  ret i1 %r
}

define i1 @gteq-int8(i8, i8) {
entry:
  %r = icmp sge i8 %0, %1
  ret i1 %r
}

define i1 @lt-int8(i8, i8) {
entry:
  %r = icmp slt i8 %0, %1
  ret i1 %r
}

define i1 @lteq-int8(i8, i8) {
entry:
  %r = icmp sle i8 %0, %1
  ret i1 %r
}

define i8 @neg-int8(i8) {
entry:
  %1 = sub i8 0, %0
  ret i8 %1
}

define i8 @add-int8(i8, i8) {
entry:
  %r = add i8 %0, %1
  ret i8 %r
}

define i8 @sub-int8(i8, i8) {
entry:
  %r = sub i8 %0, %1
  ret i8 %r
}

define i8 @mul-int8(i8, i8) {
entry:
  %r = mul i8 %0, %1
  ret i8 %r
}

define i8 @div-int8(i8, i8) {
entry:
  %r = sdiv i8 %0, %1
  ret i8 %r
}

define i8 @shl-int8(i8, i8) {
entry:
  %r = shl i8 %0, %1
  ret i8 %r
}

define i8 @shr-int8(i8, i8) {
entry:
  %r = ashr i8 %0, %1
  ret i8 %r
}

; float64

define i1 @eq-float64(double, double) {
entry:
  %r = fcmp oeq double %0, %1
  ret i1 %r
}

define i1 @neq-float64(double, double) {
entry:
  %r = fcmp one double %0, %1
  ret i1 %r
}

define i1 @gt-float64(double, double) {
entry:
  %r = fcmp ogt double %0, %1
  ret i1 %r
}

define i1 @gteq-float64(double, double) {
entry:
  %r = fcmp oge double %0, %1
  ret i1 %r
}

define i1 @lt-float64(double, double) {
entry:
  %r = fcmp olt double %0, %1
  ret i1 %r
}

define i1 @lteq-float64(double, double) {
entry:
  %r = fcmp ole double %0, %1
  ret i1 %r
}

define double @neg-float64(double) {
entry:
  %1 = fsub double 0.0, %0
  ret double %1
}

define double @add-float64(double, double) {
entry:
  %r = fadd double %0, %1
  ret double %r
}

define double @sub-float64(double, double) {
entry:
  %r = fsub double %0, %1
  ret double %r
}

define double @mul-float64(double, double) {
entry:
  %r = fmul double %0, %1
  ret double %r
}

define double @div-float64(double, double) {
entry:
  %r = fdiv double %0, %1
  ret double %r
}

; float32

define i1 @eq-float32(float, float) {
entry:
  %r = fcmp oeq float %0, %1
  ret i1 %r
}

define i1 @neq-float32(float, float) {
entry:
  %r = fcmp one float %0, %1
  ret i1 %r
}

define i1 @gt-float32(float, float) {
entry:
  %r = fcmp ogt float %0, %1
  ret i1 %r
}

define i1 @gteq-float32(float, float) {
entry:
  %r = fcmp oge float %0, %1
  ret i1 %r
}

define i1 @lt-float32(float, float) {
entry:
  %r = fcmp olt float %0, %1
  ret i1 %r
}

define i1 @lteq-float32(float, float) {
entry:
  %r = fcmp ole float %0, %1
  ret i1 %r
}

define float @neg-float32(float) {
entry:
  %1 = fsub float 0.0, %0
  ret float %1
}

define float @add-float32(float, float) {
entry:
  %r = fadd float %0, %1
  ret float %r
}

define float @sub-float32(float, float) {
entry:
  %r = fsub float %0, %1
  ret float %r
}

define float @mul-float32(float, float) {
entry:
  %r = fmul float %0, %1
  ret float %r
}

define float @div-float32(float, float) {
entry:
  %r = fdiv float %0, %1
  ret float %r
}
