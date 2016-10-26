define i1 @not-bool(i1) {
entry:
  %1 = xor i1 %0, true
  ret i1 %1
}

define i1 @and-bool(i1, i1) {
entry:
  %2 = add i1 %0, %1
  ret i1 %2
}

define i1 @or-bool(i1, i1) {
entry:
  %2 = or i1 %0, %1
  ret i1 %2
}

; int64

define i1 @eq-int64(i64, i64) {
entry:
  %2 = icmp eq i64 %0, %1
  ret i1 %2
}

define i1 @neq-int64(i64, i64) {
entry:
  %2 = icmp ne i64 %0, %1
  ret i1 %2
}

define i1 @gt-int64(i64, i64) {
entry:
  %2 = icmp sgt i64 %0, %1
  ret i1 %2
}

define i1 @gteq-int64(i64, i64) {
entry:
  %2 = icmp sge i64 %0, %1
  ret i1 %2
}

define i1 @lt-int64(i64, i64) {
entry:
  %2 = icmp slt i64 %0, %1
  ret i1 %2
}

define i1 @lteq-int64(i64, i64) {
entry:
  %2 = icmp sle i64 %0, %1
  ret i1 %2
}

define i64 @neg-int64(i64) {
entry:
  %1 = sub i64 0, %0
  ret i64 %1
}

define i64 @add-int64(i64, i64) {
entry:
  %2 = add i64 %0, %1
  ret i64 %2
}

define i64 @sub-int64(i64, i64) {
entry:
  %2 = sub i64 %0, %1
  ret i64 %2
}

define i64 @mul-int64(i64, i64) {
entry:
  %2 = mul i64 %0, %1
  ret i64 %2
}

define i64 @div-int64(i64, i64) {
entry:
  %2 = sdiv i64 %0, %1
  ret i64 %2
}

define i64 @shl-int64(i64, i64) {
entry:
  %2 = shl i64 %0, %1
  ret i64 %2
}

define i64 @shr-int64(i64, i64) {
entry:
  %2 = ashr i64 %0, %1
  ret i64 %2
}

; int32

define i1 @eq-int32(i32, i32) {
entry:
  %2 = icmp eq i32 %0, %1
  ret i1 %2
}

define i1 @neq-int32(i32, i32) {
entry:
  %2 = icmp ne i32 %0, %1
  ret i1 %2
}

define i1 @gt-int32(i32, i32) {
entry:
  %2 = icmp sgt i32 %0, %1
  ret i1 %2
}

define i1 @gteq-int32(i32, i32) {
entry:
  %2 = icmp sge i32 %0, %1
  ret i1 %2
}

define i1 @lt-int32(i32, i32) {
entry:
  %2 = icmp slt i32 %0, %1
  ret i1 %2
}

define i1 @lteq-int32(i32, i32) {
entry:
  %2 = icmp sle i32 %0, %1
  ret i1 %2
}

define i32 @neg-int32(i32) {
entry:
  %1 = sub i32 0, %0
  ret i32 %1
}

define i32 @add-int32(i32, i32) {
entry:
  %2 = add i32 %0, %1
  ret i32 %2
}

define i32 @sub-int32(i32, i32) {
entry:
  %2 = sub i32 %0, %1
  ret i32 %2
}

define i32 @mul-int32(i32, i32) {
entry:
  %2 = mul i32 %0, %1
  ret i32 %2
}

define i32 @div-int32(i32, i32) {
entry:
  %2 = sdiv i32 %0, %1
  ret i32 %2
}

define i32 @shl-int32(i32, i32) {
entry:
  %2 = shl i32 %0, %1
  ret i32 %2
}

define i32 @shr-int32(i32, i32) {
entry:
  %2 = ashr i32 %0, %1
  ret i32 %2
}

; int16

define i1 @eq-int16(i16, i16) {
entry:
  %2 = icmp eq i16 %0, %1
  ret i1 %2
}

define i1 @neq-int16(i16, i16) {
entry:
  %2 = icmp ne i16 %0, %1
  ret i1 %2
}

define i1 @gt-int16(i16, i16) {
entry:
  %2 = icmp sgt i16 %0, %1
  ret i1 %2
}

define i1 @gteq-int16(i16, i16) {
entry:
  %2 = icmp sge i16 %0, %1
  ret i1 %2
}

define i1 @lt-int16(i16, i16) {
entry:
  %2 = icmp slt i16 %0, %1
  ret i1 %2
}

define i1 @lteq-int16(i16, i16) {
entry:
  %2 = icmp sle i16 %0, %1
  ret i1 %2
}

define i16 @neg-int16(i16) {
entry:
  %1 = sub i16 0, %0
  ret i16 %1
}

define i16 @add-int16(i16, i16) {
entry:
  %2 = add i16 %0, %1
  ret i16 %2
}

define i16 @sub-int16(i16, i16) {
entry:
  %2 = sub i16 %0, %1
  ret i16 %2
}

define i16 @mul-int16(i16, i16) {
entry:
  %2 = mul i16 %0, %1
  ret i16 %2
}

define i16 @div-int16(i16, i16) {
entry:
  %2 = sdiv i16 %0, %1
  ret i16 %2
}

define i16 @shl-int16(i16, i16) {
entry:
  %2 = shl i16 %0, %1
  ret i16 %2
}

define i16 @shr-int16(i16, i16) {
entry:
  %2 = ashr i16 %0, %1
  ret i16 %2
}

; int8

define i1 @eq-int8(i8, i8) {
entry:
  %2 = icmp eq i8 %0, %1
  ret i1 %2
}

define i1 @neq-int8(i8, i8) {
entry:
  %2 = icmp ne i8 %0, %1
  ret i1 %2
}

define i1 @gt-int8(i8, i8) {
entry:
  %2 = icmp sgt i8 %0, %1
  ret i1 %2
}

define i1 @gteq-int8(i8, i8) {
entry:
  %2 = icmp sge i8 %0, %1
  ret i1 %2
}

define i1 @lt-int8(i8, i8) {
entry:
  %2 = icmp slt i8 %0, %1
  ret i1 %2
}

define i1 @lteq-int8(i8, i8) {
entry:
  %2 = icmp sle i8 %0, %1
  ret i1 %2
}

define i8 @neg-int8(i8) {
entry:
  %1 = sub i8 0, %0
  ret i8 %1
}

define i8 @add-int8(i8, i8) {
entry:
  %2 = add i8 %0, %1
  ret i8 %2
}

define i8 @sub-int8(i8, i8) {
entry:
  %2 = sub i8 %0, %1
  ret i8 %2
}

define i8 @mul-int8(i8, i8) {
entry:
  %2 = mul i8 %0, %1
  ret i8 %2
}

define i8 @div-int8(i8, i8) {
entry:
  %2 = sdiv i8 %0, %1
  ret i8 %2
}

define i8 @shl-int8(i8, i8) {
entry:
  %2 = shl i8 %0, %1
  ret i8 %2
}

define i8 @shr-int8(i8, i8) {
entry:
  %2 = ashr i8 %0, %1
  ret i8 %2
}

; float64

define i1 @eq-float64(double, double) {
entry:
  %2 = fcmp oeq double %0, %1
  ret i1 %2
}

define i1 @neq-float64(double, double) {
entry:
  %2 = fcmp one double %0, %1
  ret i1 %2
}

define i1 @gt-float64(double, double) {
entry:
  %2 = fcmp ogt double %0, %1
  ret i1 %2
}

define i1 @gteq-float64(double, double) {
entry:
  %2 = fcmp oge double %0, %1
  ret i1 %2
}

define i1 @lt-float64(double, double) {
entry:
  %2 = fcmp olt double %0, %1
  ret i1 %2
}

define i1 @lteq-float64(double, double) {
entry:
  %2 = fcmp ole double %0, %1
  ret i1 %2
}

define double @neg-float64(double) {
entry:
  %1 = fsub double 0, %0
  ret double %1
}

define double @add-float64(double, double) {
entry:
  %2 = fadd double %0, %1
  ret double %2
}

define double @sub-float64(double, double) {
entry:
  %2 = fsub double %0, %1
  ret double %2
}

define double @mul-float64(double, double) {
entry:
  %2 = fmul double %0, %1
  ret double %2
}

define double @div-float64(double, double) {
entry:
  %2 = fdiv double %0, %1
  ret double %2
}

; float32

define i1 @eq-float32(float, float) {
entry:
  %2 = fcmp oeq float %0, %1
  ret i1 %2
}

define i1 @neq-float32(float, float) {
entry:
  %2 = fcmp one float %0, %1
  ret i1 %2
}

define i1 @gt-float32(float, float) {
entry:
  %2 = fcmp ogt float %0, %1
  ret i1 %2
}

define i1 @gteq-float32(float, float) {
entry:
  %2 = fcmp oge float %0, %1
  ret i1 %2
}

define i1 @lt-float32(float, float) {
entry:
  %2 = fcmp olt float %0, %1
  ret i1 %2
}

define i1 @lteq-float32(float, float) {
entry:
  %2 = fcmp ole float %0, %1
  ret i1 %2
}

define float @neg-float32(float) {
entry:
  %1 = fsub float 0, %0
  ret float %1
}

define float @add-float32(float, float) {
entry:
  %2 = fadd float %0, %1
  ret float %2
}

define float @sub-float32(float, float) {
entry:
  %2 = fsub float %0, %1
  ret float %2
}

define float @mul-float32(float, float) {
entry:
  %2 = fmul float %0, %1
  ret float %2
}

define float @div-float32(float, float) {
entry:
  %2 = fdiv float %0, %1
  ret float %2
}
