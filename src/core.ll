define i64 @neg-int64(i64) {
entry:
  %1 = sub i64 0, %0
  ret i64 %1
}

define i1 @not-bool(i1) {
entry:
  %1 = xor i1 %0, true
  ret i1 %1
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