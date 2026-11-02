#include "passport_monitor.h"
#include <HsFFI.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define Z32 "0000000000000000000000000000000000000000000000000000000000000000"
#define Z64 Z32 Z32
/* State token labels (in wire order):
 * BEFORE prefix: stateRound=0, authNonce=0, deviceEpoch=0, deviceCount=0,
 *                devices=[] (count 0), balances={} (count 0).
 * AFTER prefix:  stateRound=1, authNonce=0, deviceEpoch=0, deviceCount=0,
 *                devices=[] (count 0), balances={Z32:7} (count 1, key, value).
 * TAIL: encKey=Z32, recoveryPk=(0,1), phi=absent (marker 0), phiLen=0,
 *       session=Z32, wrap=Z64, pending=false (0), pendingEntry=Z32,
 *       pendingRecoveryPk=(0,1), pendingNotBefore=0, vetoWindow=0.
 * Thus deposit Z32 7 changes only stateRound (0 -> 1) and balances.
 */
#define TAIL Z32 " 0 1 0 0 " Z32 " " Z64 " 0 " Z32 " 0 1 0 0"
#define BEFORE "0 0 0 0 0 0 " TAIL
#define AFTER "1 0 0 0 0 1 " Z32 " 7 " TAIL
/* call: logical account 0, blockTime 0; D: deposit; ok: observed acceptance.
 * The Z32 after source is the crypto domain, not the logical account. */
#define OBSERVATION "monitor-v1 source " Z32 " " BEFORE " call 0 0 D " Z32 " 7 ok " AFTER
#define WRONG "monitor-v1 source " Z32 " " BEFORE " call 0 0 D " Z32 " 7 ok " BEFORE
#define SIGNED "monitor-v1 source " Z32 " " BEFORE " call 0 0 J C 1 2 0 1 2 1 0 ok " BEFORE
#define PREPARE "prepare source " Z32 " 0 " BEFORE " D " Z32 " 7"

static void require(int condition, const char *message) {
  if (!condition) { fprintf(stderr, "C monitor smoke: %s\n", message); exit(1); }
}

/* Minimal check/error/free usage; call only between hs_init and hs_exit.
 * NULL backend is sufficient for this deposit, which demands no crypto.
 * Signed/recovery calls instead need an actual deterministic crypto callback. */
static int check_example(const char *observation) {
  uint8_t *output = NULL;
  size_t length = 0;
  int status = passport_monitor_check((const uint8_t *)observation, strlen(observation),
                                     NULL, NULL, &output, &length);
  if (status == PASSPORT_MONITOR_TRUE) {
    /* Outcome AND final state match, including a matching rejection/abort. */
  } else if (status == PASSPORT_MONITOR_FALSE) {
    fputs("Observation disagrees with the model\n", stderr);
  } else {
    fprintf(stderr, "Monitor error %d: ", status);
    if (output != NULL) fwrite(output, 1, length, stderr);
    fputc('\n', stderr);
  }
  /* Every non-NULL output, including error text, must use this allocator. */
  passport_monitor_free(output);
  return status;
}

/* Regression-only callbacks and cases below are not production backends.
 * These deliberately failing/malformed backends never fake successful crypto. */
static int failing(void *userdata, const uint8_t *request, size_t length,
                   const uint8_t **reply, size_t *reply_length) {
  int *calls = (int *)userdata;
  static const uint8_t message[] = "deliberate backend failure";
  require(request != NULL && length != 0, "callback receives request");
  ++*calls;
  *reply = message; *reply_length = sizeof(message) - 1;
  return 1;
}
static int malformed(void *userdata, const uint8_t *request, size_t length,
                     const uint8_t **reply, size_t *reply_length) {
  static const uint8_t message[] = "not a point or digest";
  (void)request; (void)length;
  ++*(int *)userdata;
  *reply = message; *reply_length = sizeof(message) - 1;
  return 0;
}

int main(int argc, char **argv) {
  uint8_t *output = NULL, *candidate = NULL;
  size_t length = 0, candidate_length = 0;
  int calls = 0, status;
  hs_init(&argc, &argv);
  require(check_example(OBSERVATION) == PASSPORT_MONITOR_TRUE, "minimal deposit example");

  /* Regression cases: verdicts, normalization, ownership, and backend errors. */
  for (int i = 0; i < 32; ++i) {
    status = passport_monitor_check((const uint8_t *)OBSERVATION, strlen(OBSERVATION),
                                   failing, &calls, &output, &length);
    require(status == PASSPORT_MONITOR_TRUE && output == NULL && length == 0, "actual deposit true");
    require(calls == 0, "deposit must not invoke crypto");
    status = passport_monitor_check((const uint8_t *)WRONG, strlen(WRONG),
                                   NULL, NULL, &output, &length);
    require(status == PASSPORT_MONITOR_FALSE && output == NULL, "wrong poststate is false, not error");
    status = passport_monitor_normalize((const uint8_t *)OBSERVATION, strlen(OBSERVATION), &output, &length);
    require(status == 0 && output != NULL && output[length] == 0, "canonical output owned and terminated");
    require(length == strlen(OBSERVATION) && memcmp(output, OBSERVATION, length) == 0, "canonical serialization");
    uint8_t *canonical = output;
    size_t canonical_length = length;
    status = passport_monitor_check(canonical, canonical_length, NULL, NULL, &output, &length);
    require(status == 0 && output == NULL, "owned canonical buffer can be consumed");
    passport_monitor_free(canonical);
  }
  status = passport_monitor_check((const uint8_t *)"monitor-v1 invalid", 18,
                                 NULL, NULL, &output, &length);
  require(status == PASSPORT_MONITOR_MALFORMED && output != NULL && length != 0, "malformed distinct with owned error");
  passport_monitor_free(output);
  status = passport_monitor_check((const uint8_t *)SIGNED, strlen(SIGNED),
                                 failing, &calls, &output, &length);
  require(status == PASSPORT_MONITOR_BACKEND_ERROR && calls > 0 && output != NULL, "callback failure not false");
  passport_monitor_free(output);
  calls = 0;
  status = passport_monitor_check((const uint8_t *)SIGNED, strlen(SIGNED),
                                 malformed, &calls, &output, &length);
  require(status == PASSPORT_MONITOR_BACKEND_ERROR && calls > 0, "malformed primitive not false");
  passport_monitor_free(output);
  status = passport_monitor_check((const uint8_t *)SIGNED, strlen(SIGNED),
                                 NULL, NULL, &output, &length);
  require(status == PASSPORT_MONITOR_BACKEND_ERROR, "missing crypto explicitly fails when demanded");
  passport_monitor_free(output);
  status = passport_monitor_prepare((const uint8_t *)PREPARE, strlen(PREPARE),
                                   NULL, NULL, &candidate, &candidate_length);
  require(status == 0 && candidate != NULL && candidate_length > 0, "actual Agda candidate generation");
  size_t capacity = candidate_length + strlen(OBSERVATION) + 64;
  char *admission = malloc(capacity);
  require(admission != NULL, "allocate admission input");
  int written = snprintf(admission, capacity, "monitor-v1 source " Z32 " " BEFORE " admit 0 0 %.*s ok " AFTER,
                         (int)candidate_length, (const char *)candidate);
  require(written > 0 && (size_t)written < capacity, "admission input size");
  status = passport_monitor_check((const uint8_t *)admission, (size_t)written,
                                 NULL, NULL, &output, &length);
  require(status == 0, "prepared candidate actually admits");
  free(admission);
  passport_monitor_free(candidate);
  passport_monitor_free(NULL);
  status = passport_monitor_check(NULL, 1, NULL, NULL, &output, &length);
  require(status == PASSPORT_MONITOR_MALFORMED, "invalid pointer/length pair rejected");
  passport_monitor_free(output);
  const char *aborting = "prepare source " Z32 " 0 " BEFORE " F";
  status = passport_monitor_prepare((const uint8_t *)aborting, strlen(aborting),
                                   NULL, NULL, &output, &length);
  require(status == PASSPORT_MONITOR_BUILD_ABORTED && output != NULL &&
          length == strlen("noPending") && memcmp(output, "noPending", length) == 0,
          "preparation abort distinct from malformed/backend/false");
  passport_monitor_free(output);
  status = passport_monitor_normalize((const uint8_t *)OBSERVATION, strlen(OBSERVATION), NULL, &length);
  require(status == PASSPORT_MONITOR_MALFORMED, "null output pointer rejected");
  hs_exit();
  puts("C monitor smoke PASS (model true/false, codec, candidate, malformed, backend, ownership)");
  return 0;
}
