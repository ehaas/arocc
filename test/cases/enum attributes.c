enum E {
   is_deprecated __attribute__((deprecated)),
   is_deprecated_with_msg __attribute__((deprecated("I am deprecated"))),
   is_unavailable __attribute__((unavailable)),
   is_unavailable_with_msg  __attribute__((unavailable("I am not available"))),
   newval,
};

void foo(void) {
  int a = newval;
  a = is_deprecated;
  a = is_deprecated_with_msg;
  a = is_unavailable;
  a = is_unavailable_with_msg;
}

#define EXPECTED_ERRORS "enum attributes.c:11:7: warning: 'is_deprecated' is deprecated [-Wdeprecated-declarations]" \
  "enum attributes.c:2:4: note: 'is_deprecated' has been explicitly marked deprecated here" \
  "enum attributes.c:12:7: warning: 'is_deprecated_with_msg' is deprecated: I am deprecated [-Wdeprecated-declarations]" \
  "enum attributes.c:3:4: note: 'is_deprecated_with_msg' has been explicitly marked deprecated here" \
  "enum attributes.c:13:7: error: 'is_unavailable' is unavailable" \
  "enum attributes.c:4:4: note: 'is_unavailable' has been explicitly marked unavailable here" \
  "enum attributes.c:14:7: error: 'is_unavailable_with_msg' is unavailable: I am not available" \
  "enum attributes.c:5:4: note: 'is_unavailable_with_msg' has been explicitly marked unavailable here" \
