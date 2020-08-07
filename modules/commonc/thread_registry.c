#include "paracooba/common/status.h"
#include <paracooba/common/linked_list.h>
#include <paracooba/common/thread_registry.h>

#include <parac_common_export.h>

#include <assert.h>
#include <stdlib.h>

#ifdef __STDC_NO_THREADS__
// C11 Threads not available, using c11threads from
// https://github.com/jtsiomb/c11thread0s
#include "c11threads.h"
#else
#include <threads.h>
#endif

typedef struct thread_handle {
  parac_thread_registry_handle registry_handle;
  thrd_t thread;
} thread_handle;

PARAC_LINKED_LIST(thread_handle, thread_handle)
PARAC_LINKED_LIST(thread_registry_new_thread_starting_cb,
                  parac_thread_registry_new_thread_starting_cb)

PARAC_COMMON_EXPORT
void
parac_thread_registry_init(parac_thread_registry* registry) {
  assert(registry);

  registry->threads = malloc(sizeof(parac_thread_handle_list));
  registry->new_thread_starting_cbs =
    malloc(sizeof(parac_thread_registry_new_thread_starting_cb_list));

  assert(registry->threads);
  assert(registry->new_thread_starting_cbs);

  parac_thread_handle_list_init(registry->threads);
  parac_thread_registry_new_thread_starting_cb_list_init(
    registry->new_thread_starting_cbs);
}

PARAC_COMMON_EXPORT
void
parac_thread_registry_free(parac_thread_registry* registry) {
  assert(registry);
  assert(registry->threads);
  assert(registry->new_thread_starting_cbs);

  parac_thread_handle_list_free(registry->threads);
  parac_thread_registry_new_thread_starting_cb_list_free(
    registry->new_thread_starting_cbs);

  free(registry->threads);
  free(registry->new_thread_starting_cbs);
}

static int
run_wrapper(parac_thread_registry_handle* handle) {
  int returncode = 0;
  handle->running = true;
  returncode = handle->start_func(handle);
  handle->running = false;
  return returncode;
}

PARAC_COMMON_EXPORT
parac_status
parac_thread_registry_create(parac_thread_registry* registry,
                             struct parac_module* starter,
                             parac_thread_registry_start_func start_func,
                             parac_thread_registry_handle** out_handle) {
  assert(registry);
  assert(start_func);

  thread_handle* thandle =
    parac_thread_handle_list_alloc_new(registry->threads);
  if(!thandle) {
    return PARAC_OUT_OF_MEMORY;
  }

  parac_thread_registry_handle* handle = &thandle->registry_handle;
  handle->stop = false;
  handle->running = false;
  handle->thread_id = registry->threads->size;
  handle->starter = starter;
  handle->start_func = start_func;

  struct parac_thread_registry_new_thread_starting_cb_list_entry* cb =
    registry->new_thread_starting_cbs->first;
  while(cb) {
    if(cb->entry) {
      cb->entry(handle);
    }
    cb = cb->next;
  }

  int success =
    thrd_create(&thandle->thread, (int (*)(void*))run_wrapper, handle);
  if(success == thrd_success) {
    if(out_handle) {
      *out_handle = handle;
    }
    return PARAC_OK;
  } else if(success == thrd_nomem) {
    return PARAC_OUT_OF_MEMORY;
  } else {
    return PARAC_GENERIC_ERROR;
  }
}

PARAC_COMMON_EXPORT
void
parac_thread_registry_stop(parac_thread_registry* registry) {
  struct parac_thread_handle_list_entry* handle = registry->threads->first;
  while(handle) {
    handle->entry.registry_handle.stop = true;
    handle = handle->next;
  }
}

PARAC_COMMON_EXPORT
void
parac_thread_registry_wait_for_exit(parac_thread_registry* registry) {
  struct parac_thread_handle_list_entry* handle = registry->threads->first;
  while(handle) {
    thrd_join(handle->entry.thread, &handle->entry.registry_handle.exit_status);
    handle = handle->next;
  }
}
