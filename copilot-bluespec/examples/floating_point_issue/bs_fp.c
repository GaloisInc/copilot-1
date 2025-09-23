#include <math.h>

union ui_float {
  unsigned int i;
  float f;
};

union ull_double {
  unsigned long long i;
  double f;
};

unsigned int bs_fp_expf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = expf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_exp(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = exp(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_logf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = logf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_log(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = log(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_acosf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = acosf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_acos(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = acos(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_asinf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = asinf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_asin(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = asin(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_atanf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = atanf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_atan(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = atan(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_cosf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = cosf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_cos(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = cos(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_sinf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = sinf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_sin(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = sin(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_tanf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = tanf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_tan(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = tan(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_acoshf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = acoshf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_acosh(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = acosh(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_asinhf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = asinhf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_asinh(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = asinh(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_atanhf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = atanhf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_atanh(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = atanh(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_coshf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = coshf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_cosh(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = cosh(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_sinhf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = sinhf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_sinh(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = sinh(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_tanhf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = tanhf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_tanh(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = tanh(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_ceilf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = ceilf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_ceil(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = ceil(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_floorf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = floorf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_floor(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = floor(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_sqrtf(unsigned int x) {
  union ui_float x_u;
  union ui_float r_u;
  x_u.i = x;
  r_u.f = sqrtf(x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_sqrt(unsigned long long x) {
  union ull_double x_u;
  union ull_double r_u;
  x_u.i = x;
  r_u.f = sqrt(x_u.f);
  return r_u.i;
}

unsigned int bs_fp_powf(unsigned int x, unsigned int y) {
  union ui_float x_u;
  union ui_float y_u;
  union ui_float r_u;
  x_u.i = x;
  y_u.i = y;
  r_u.f = powf(x_u.f, y_u.f);
  return r_u.i;
}

unsigned long long bs_fp_pow(unsigned long long x, unsigned long long y) {
  union ull_double x_u;
  union ull_double y_u;
  union ull_double r_u;
  x_u.i = x;
  y_u.i = y;
  r_u.f = pow(x_u.f, y_u.f);
  return r_u.i;
}

unsigned int bs_fp_atan2f(unsigned int x, unsigned int y) {
  union ui_float x_u;
  union ui_float y_u;
  union ui_float r_u;
  x_u.i = x;
  y_u.i = y;
  r_u.f = atan2f(x_u.f, y_u.f);
  return r_u.i;
}

unsigned long long bs_fp_atan2(unsigned long long x, unsigned long long y) {
  union ull_double x_u;
  union ull_double y_u;
  union ull_double r_u;
  x_u.i = x;
  y_u.i = y;
  r_u.f = atan2(x_u.f, y_u.f);
  return r_u.i;
}

unsigned int bs_fp_logbf(unsigned int x, unsigned int y) {
  union ui_float x_u;
  union ui_float y_u;
  union ui_float r_u;
  x_u.i = x;
  y_u.i = y;
  r_u.f = logf(y_u.f) / logf( x_u.f);
  return r_u.i;
}

unsigned long long bs_fp_logb(unsigned long long x, unsigned long long y) {
  union ull_double x_u;
  union ull_double y_u;
  union ull_double r_u;
  x_u.i = x;
  y_u.i = y;
  r_u.f = log(y_u.f) / log( x_u.f);
  return r_u.i;
}

