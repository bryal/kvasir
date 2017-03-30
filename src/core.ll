define i1 @not-bool(i1) {
entry:
  %1 = xor i1 %0, true
  ret i1 %1
}

define i1 @and-bool({i1, i1}) {
entry:
  %a = extractvalue {i1, i1} %0, 0
  %b = extractvalue {i1, i1} %0, 1
  %r = add i1 %a, %b
  ret i1 %r
}

define i1 @or-bool({i1, i1}) {
entry:
  %a = extractvalue {i1, i1} %0, 0
  %b = extractvalue {i1, i1} %0, 1
  %r = or i1 %a, %b
  ret i1 %r
}

; int64

define i1 @eq-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = icmp eq i64 %a, %b
  ret i1 %r
}

define i1 @neq-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = icmp ne i64 %a, %b
  ret i1 %r
}

define i1 @gt-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = icmp sgt i64 %a, %b
  ret i1 %r
}

define i1 @gteq-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = icmp sge i64 %a, %b
  ret i1 %r
}

define i1 @lt-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = icmp slt i64 %a, %b
  ret i1 %r
}

define i1 @lteq-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = icmp sle i64 %a, %b
  ret i1 %r
}

define i64 @neg-int64(i64) {
entry:
  %1 = sub i64 0, %0
  ret i64 %1
}

define i64 @add-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = add i64 %a, %b
  ret i64 %r
}

define i64 @sub-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = sub i64 %a, %b
  ret i64 %r
}

define i64 @mul-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = mul i64 %a, %b
  ret i64 %r
}

define i64 @div-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = sdiv i64 %a, %b
  ret i64 %r
}

define i64 @shl-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = shl i64 %a, %b
  ret i64 %r
}

define i64 @shr-int64({i64, i64}) {
entry:
  %a = extractvalue {i64, i64} %0, 0
  %b = extractvalue {i64, i64} %0, 1
  %r = ashr i64 %a, %b
  ret i64 %r
}

; int32

define i1 @eq-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = icmp eq i32 %a, %b
  ret i1 %r
}

define i1 @neq-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = icmp ne i32 %a, %b
  ret i1 %r
}

define i1 @gt-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = icmp sgt i32 %a, %b
  ret i1 %r
}

define i1 @gteq-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = icmp sge i32 %a, %b
  ret i1 %r
}

define i1 @lt-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = icmp slt i32 %a, %b
  ret i1 %r
}

define i1 @lteq-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = icmp sle i32 %a, %b
  ret i1 %r
}

define i32 @neg-int32(i32) {
entry:
  %1 = sub i32 0, %0
  ret i32 %1
}

define i32 @add-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = add i32 %a, %b
  ret i32 %r
}

define i32 @sub-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = sub i32 %a, %b
  ret i32 %r
}

define i32 @mul-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = mul i32 %a, %b
  ret i32 %r
}

define i32 @div-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = sdiv i32 %a, %b
  ret i32 %r
}

define i32 @shl-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = shl i32 %a, %b
  ret i32 %r
}

define i32 @shr-int32({i32, i32}) {
entry:
  %a = extractvalue {i32, i32} %0, 0
  %b = extractvalue {i32, i32} %0, 1
  %r = ashr i32 %a, %b
  ret i32 %r
}

; int16

define i1 @eq-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = icmp eq i16 %a, %b
  ret i1 %r
}

define i1 @neq-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = icmp ne i16 %a, %b
  ret i1 %r
}

define i1 @gt-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = icmp sgt i16 %a, %b
  ret i1 %r
}

define i1 @gteq-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = icmp sge i16 %a, %b
  ret i1 %r
}

define i1 @lt-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = icmp slt i16 %a, %b
  ret i1 %r
}

define i1 @lteq-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = icmp sle i16 %a, %b
  ret i1 %r
}

define i16 @neg-int16(i16) {
entry:
  %1 = sub i16 0, %0
  ret i16 %1
}

define i16 @add-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = add i16 %a, %b
  ret i16 %r
}

define i16 @sub-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = sub i16 %a, %b
  ret i16 %r
}

define i16 @mul-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = mul i16 %a, %b
  ret i16 %r
}

define i16 @div-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = sdiv i16 %a, %b
  ret i16 %r
}

define i16 @shl-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = shl i16 %a, %b
  ret i16 %r
}

define i16 @shr-int16({i16, i16}) {
entry:
  %a = extractvalue {i16, i16} %0, 0
  %b = extractvalue {i16, i16} %0, 1
  %r = ashr i16 %a, %b
  ret i16 %r
}

; int8

define i1 @eq-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = icmp eq i8 %a, %b
  ret i1 %r
}

define i1 @neq-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = icmp ne i8 %a, %b
  ret i1 %r
}

define i1 @gt-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = icmp sgt i8 %a, %b
  ret i1 %r
}

define i1 @gteq-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = icmp sge i8 %a, %b
  ret i1 %r
}

define i1 @lt-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = icmp slt i8 %a, %b
  ret i1 %r
}

define i1 @lteq-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = icmp sle i8 %a, %b
  ret i1 %r
}

define i8 @neg-int8(i8) {
entry:
  %1 = sub i8 0, %0
  ret i8 %1
}

define i8 @add-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = add i8 %a, %b
  ret i8 %r
}

define i8 @sub-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = sub i8 %a, %b
  ret i8 %r
}

define i8 @mul-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = mul i8 %a, %b
  ret i8 %r
}

define i8 @div-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = sdiv i8 %a, %b
  ret i8 %r
}

define i8 @shl-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = shl i8 %a, %b
  ret i8 %r
}

define i8 @shr-int8({i8, i8}) {
entry:
  %a = extractvalue {i8, i8} %0, 0
  %b = extractvalue {i8, i8} %0, 1
  %r = ashr i8 %a, %b
  ret i8 %r
}

; float64

define i1 @eq-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fcmp oeq double %a, %b
  ret i1 %r
}

define i1 @neq-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fcmp one double %a, %b
  ret i1 %r
}

define i1 @gt-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fcmp ogt double %a, %b
  ret i1 %r
}

define i1 @gteq-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fcmp oge double %a, %b
  ret i1 %r
}

define i1 @lt-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fcmp olt double %a, %b
  ret i1 %r
}

define i1 @lteq-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fcmp ole double %a, %b
  ret i1 %r
}

define double @neg-float64(double) {
entry:
  %1 = fsub double 0.0, %0
  ret double %1
}

define double @add-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fadd double %a, %b
  ret double %r
}

define double @sub-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fsub double %a, %b
  ret double %r
}

define double @mul-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fmul double %a, %b
  ret double %r
}

define double @div-float64({double, double}) {
entry:
  %a = extractvalue {double, double} %0, 0
  %b = extractvalue {double, double} %0, 1
  %r = fdiv double %a, %b
  ret double %r
}

; float32

define i1 @eq-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fcmp oeq float %a, %b
  ret i1 %r
}

define i1 @neq-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fcmp one float %a, %b
  ret i1 %r
}

define i1 @gt-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fcmp ogt float %a, %b
  ret i1 %r
}

define i1 @gteq-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fcmp oge float %a, %b
  ret i1 %r
}

define i1 @lt-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fcmp olt float %a, %b
  ret i1 %r
}

define i1 @lteq-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fcmp ole float %a, %b
  ret i1 %r
}

define float @neg-float32(float) {
entry:
  %1 = fsub float 0.0, %0
  ret float %1
}

define float @add-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fadd float %a, %b
  ret float %r
}

define float @sub-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fsub float %a, %b
  ret float %r
}

define float @mul-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fmul float %a, %b
  ret float %r
}

define float @div-float32({float, float}) {
entry:
  %a = extractvalue {float, float} %0, 0
  %b = extractvalue {float, float} %0, 1
  %r = fdiv float %a, %b
  ret float %r
}
