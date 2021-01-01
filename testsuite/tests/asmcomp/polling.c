#define CAML_NAME_SPACE
#define CAML_INTERNALS

#include <caml/domain.h>
#include <caml/signals.h>

CAMLprim value request_minor_gc(value v) {
  caml_request_minor_gc();
}

CAMLprim value minor_gcs(value v) {
  return Val_long(Caml_state->stat_minor_collections);
}