#ifndef PASSPORT_MONITOR_H
#define PASSPORT_MONITOR_H
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

/* Initialize the GHC RTS with hs_init before calling; stop all monitor calls and
 * release outputs before hs_exit. Include HsFFI.h from the selected GHC toolchain.
 * Calls are synchronous and reentrant. Concurrent calls need independent callback
 * state or a thread-safe backend. No library-global backend or stdin is used. */
typedef enum passport_monitor_status {
  PASSPORT_MONITOR_TRUE = 0,       /* consistent observation; also normalize/prepare success */
  PASSPORT_MONITOR_FALSE = 1,      /* well-formed observation, model disagrees */
  PASSPORT_MONITOR_MALFORMED = 2,
  PASSPORT_MONITOR_BACKEND_ERROR = 3,
  PASSPORT_MONITOR_INTERNAL_ERROR = 4,
  PASSPORT_MONITOR_BUILD_ABORTED = 5
} passport_monitor_status;

/* Deterministic crypto callback, using the entry/challenge/mulg/mul/add token
 * protocol in docs/conformance-recovery.md, "Runtime transition monitor".
 * Return 0 and an exact hex32 digest or decimal affine point (two naturals);
 * nonzero means backend failure and the reply is optional UTF-8 error text.
 * Never substitute fake primitives in production.
 *
 * request is borrowed for the callback duration only, and is NOT NUL-terminated.
 * Set *reply and *reply_length to a borrowed byte buffer. It must remain valid
 * until the NEXT callback on this operation or until the monitor call returns.
 * The library copies it before either event; it NEVER frees callback memory.
 * A NULL reply is allowed only with zero length. Callback/userdata lifetimes
 * must cover the outer call. Do not throw exceptions/longjmp across this ABI.
 *
 * The generated Agda API is pure; a narrow NOINLINE deterministic IO bridge is
 * used internally. Pure evaluation may share identical primitive computations;
 * callbacks MUST NOT depend on invocation count, time, or mutable crypto state.
 */
typedef int (*passport_monitor_backend)(void *userdata,
  const uint8_t *request, size_t request_length,
  const uint8_t **reply, size_t *reply_length);

/* All inputs are length-delimited UTF-8, never retained. Output pointers MUST be
 * non-NULL. On entry *output=NULL,*output_length=0 (except if pointers invalid).
 * check returns no output on true/false. TRUE means the observed outcome AND
 * final state match, including a correctly observed rejection or abort; it does
 * not mean the transaction was accepted. FALSE means a model discrepancy.
 * normalize/prepare return serialized tokens on success. Every error normally
 * returns diagnostic text (build-abort returns its normalized model error code).
 * Allocation failure may return INTERNAL_ERROR with no text.
 *
 * Every non-NULL output is library-allocated, uniquely owned by the caller,
 * NUL-terminated for convenience (length excludes NUL), and must be released
 * exactly once with passport_monitor_free, including error strings. Never free
 * it with another allocator. passport_monitor_free(NULL) is allowed.
 * No Haskell exception escapes the ABI. Backend errors never become FALSE.
 */
int passport_monitor_check(const uint8_t *observation, size_t length,
  passport_monitor_backend backend, void *userdata,
  uint8_t **output, size_t *output_length);
int passport_monitor_normalize(const uint8_t *observation, size_t length,
  uint8_t **output, size_t *output_length);
/* Input: prepare VARIANT SELF TX_ACCOUNT <build-state> <raw-call>.
 * SELF is the hex32 crypto domain; TX_ACCOUNT is the natural logical account.
 * Output: TX_ACCOUNT <build-state> <raw-call> J COUNT <events...>.
 * This prepares model-side evidence; it does not decode a Compact transcript
 * or check admission against a current context/state. */
int passport_monitor_prepare(const uint8_t *request, size_t length,
  passport_monitor_backend backend, void *userdata,
  uint8_t **output, size_t *output_length);
void passport_monitor_free(uint8_t *output);
#ifdef __cplusplus
}
#endif
#endif
