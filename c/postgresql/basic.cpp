/*
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
*/
#include <lean/lean.h>
#include <libpq-fe.h>
#include <poll.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

/*
Thread safety: libpq allows a `PGconn` and the `PGresult`s it produced to be used from one thread
at a time. Nothing here locks, so the Lean side has to make sure that no two threads use the same
connection concurrently, e.g. by handing each thread its own connection.

Ownership: every Lean argument is borrowed (`b_lean_obj_arg`), matching the `@&` annotations on the
Lean side, and every `PGconn` and `PGresult` is owned by exactly one Lean external object whose
finalizer releases it. A connection may also be released early through `c_PQfinish`, after which
the external object holds a null pointer; every entry point checks for that rather than passing a
null connection to libpq.
*/

static void PGconn_finalizer(void* conn) {
    if (conn) {
        PQfinish((PGconn*) conn);
    }
}

static void PGresult_finalizer(void* result) {
    if (result) {
        PQclear((PGresult*) result);
    }
}

static void noop_foreach(void*, b_lean_obj_arg) {}

// A function-local static is initialised exactly once, even when several threads open their first
// connection at the same time.
static lean_external_class* PGconn_class() {
    static lean_external_class* cls = lean_register_external_class(PGconn_finalizer, noop_foreach);
    return cls;
}

static lean_external_class* PGresult_class() {
    static lean_external_class* cls =
        lean_register_external_class(PGresult_finalizer, noop_foreach);
    return cls;
}

static inline lean_object* box_PGconn(PGconn* conn) {
    return lean_alloc_external(PGconn_class(), conn);
}

static inline lean_object* box_PGresult(PGresult* result) {
    return lean_alloc_external(PGresult_class(), result);
}

static inline PGconn* unbox_PGconn(b_lean_obj_arg o) {
    return (PGconn*) lean_get_external_data(o);
}

static inline PGresult* unbox_PGresult(b_lean_obj_arg o) {
    return (PGresult*) lean_get_external_data(o);
}

static inline lean_obj_res make_error(const char* err_msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(err_msg)));
}

static const char* closed_message = "the PostgreSQL connection has been closed";

static inline lean_obj_res closed_error() {
    return make_error(closed_message);
}

// libpq hands back a null pointer for a string it does not have; Lean has no null string.
static inline lean_object* mk_string_or_empty(const char* s) {
    return lean_mk_string(s ? s : "");
}

static inline lean_object* mk_some(lean_object* v) {
    lean_object* r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}

static inline lean_object* mk_none() {
    return lean_box(0);
}

/* Connections */

extern "C" lean_obj_res c_PQconnectdb(b_lean_obj_arg s_) {
    PGconn* conn = PQconnectdb(lean_string_cstr(s_));
    if (!conn) {
        return make_error("failed to allocate a PostgreSQL connection");
    }
    return lean_io_result_mk_ok(box_PGconn(conn));
}

// CONNECTION_OK is 0, CONNECTION_BAD is 1; a closed connection reports CONNECTION_BAD.
extern "C" uint8_t c_PQstatus(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    return conn ? (uint8_t) PQstatus(conn) : (uint8_t) CONNECTION_BAD;
}

extern "C" lean_obj_res c_PQerrorMessage(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    return mk_string_or_empty(conn ? PQerrorMessage(conn) : closed_message);
}

// Close the connection now rather than when the garbage collector gets to it. Closing twice is
// harmless: the second call finds nothing to close.
extern "C" lean_obj_res c_PQfinish(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    if (conn) {
        PQfinish(conn);
        lean_to_external(conn_)->m_data = NULL;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" lean_obj_res c_PQreset(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    if (!conn) {
        return closed_error();
    }
    PQreset(conn);
    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" lean_obj_res c_PQserverVersion(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    if (!conn) {
        return closed_error();
    }
    return lean_io_result_mk_ok(lean_unsigned_to_nat((unsigned) PQserverVersion(conn)));
}

// PQTRANS_IDLE 0, PQTRANS_ACTIVE 1, PQTRANS_INTRANS 2, PQTRANS_INERROR 3, PQTRANS_UNKNOWN 4.
extern "C" uint8_t c_PQtransactionStatus(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    return conn ? (uint8_t) PQtransactionStatus(conn) : (uint8_t) PQTRANS_UNKNOWN;
}

extern "C" lean_obj_res c_PQsocket(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    if (!conn) {
        return closed_error();
    }
    int sock = PQsocket(conn);
    if (sock < 0) {
        return make_error("the PostgreSQL connection has no open socket");
    }
    return lean_io_result_mk_ok(lean_unsigned_to_nat((unsigned) sock));
}

/* Statements */

// libpq returns a null result when it is out of memory or the connection is gone; the reason is
// then only on the connection.
static lean_obj_res result_or_error(PGconn* conn, PGresult* res) {
    if (!res) {
        return make_error(PQerrorMessage(conn));
    }
    return lean_io_result_mk_ok(box_PGresult(res));
}

extern "C" lean_obj_res c_PQexec(b_lean_obj_arg conn_, b_lean_obj_arg query_) {
    PGconn* conn = unbox_PGconn(conn_);
    if (!conn) {
        return closed_error();
    }
    return result_or_error(conn, PQexec(conn, lean_string_cstr(query_)));
}

// Run `query` with `params : Array (Option String)` bound to `$1`, `$2`, ..., all sent and
// received as text. A `none` is `NULL`. The server infers the parameter types from their use.
extern "C" lean_obj_res c_PQexecParams(b_lean_obj_arg conn_, b_lean_obj_arg query_,
        b_lean_obj_arg params_) {
    PGconn* conn = unbox_PGconn(conn_);
    if (!conn) {
        return closed_error();
    }
    size_t n = lean_array_size(params_);
    if (n > 65535) {
        return make_error("a statement can take at most 65535 parameters");
    }
    // Plain C allocation: the Lean toolchain links no C++ standard library.
    const char** values = n ? (const char**) malloc(n * sizeof(const char*)) : NULL;
    if (n && !values) {
        return make_error("out of memory");
    }
    for (size_t i = 0; i < n; i++) {
        lean_object* p = lean_array_get_core(params_, i);
        // `none` is the scalar `lean_box(0)`; `some s` is a constructor holding `s`.
        values[i] = lean_is_scalar(p) ? NULL : lean_string_cstr(lean_ctor_get(p, 0));
    }
    PGresult* res = PQexecParams(conn, lean_string_cstr(query_), (int) n, NULL, values, NULL,
        NULL, 0);
    free(values);
    return result_or_error(conn, res);
}

/* Results */

extern "C" lean_obj_res c_PQresultStatus(b_lean_obj_arg result_) {
    return mk_string_or_empty(PQresStatus(PQresultStatus(unbox_PGresult(result_))));
}

extern "C" lean_obj_res c_PQresultErrorMessage(b_lean_obj_arg result_) {
    return mk_string_or_empty(PQresultErrorMessage(unbox_PGresult(result_)));
}

// One field of an error report, by its `PG_DIAG_*` code ('C' is the SQLSTATE); empty when the
// result carries no such field.
extern "C" lean_obj_res c_PQresultErrorField(b_lean_obj_arg result_, uint32_t fieldcode) {
    return mk_string_or_empty(PQresultErrorField(unbox_PGresult(result_), (int) fieldcode));
}

// The number of rows a statement affected, as libpq reports it: a decimal string, empty for a
// statement to which it does not apply.
extern "C" lean_obj_res c_PQcmdTuples(b_lean_obj_arg result_) {
    return mk_string_or_empty(PQcmdTuples(unbox_PGresult(result_)));
}

extern "C" uint32_t c_PQntuples(b_lean_obj_arg result_) {
    return PQntuples(unbox_PGresult(result_));
}

extern "C" uint32_t c_PQnfields(b_lean_obj_arg result_) {
    return PQnfields(unbox_PGresult(result_));
}

extern "C" lean_obj_res c_PQfname(b_lean_obj_arg result_, uint32_t columnNumber) {
    return mk_string_or_empty(PQfname(unbox_PGresult(result_), columnNumber));
}

extern "C" uint32_t c_PQftable(b_lean_obj_arg result_, uint32_t columnNumber) {
    return PQftable(unbox_PGresult(result_), columnNumber);
}

extern "C" int32_t c_PQfnumber(b_lean_obj_arg result_, b_lean_obj_arg columnName_) {
    return PQfnumber(unbox_PGresult(result_), lean_string_cstr(columnName_));
}

extern "C" uint32_t c_PQgetisnull(b_lean_obj_arg result_, uint32_t rowNumber,
        uint32_t columnNumber) {
    return PQgetisnull(unbox_PGresult(result_), rowNumber, columnNumber);
}

extern "C" uint32_t c_PQgetlength(b_lean_obj_arg result_, uint32_t rowNumber,
        uint32_t columnNumber) {
    return PQgetlength(unbox_PGresult(result_), rowNumber, columnNumber);
}

extern "C" lean_obj_res c_PQgetvalue(b_lean_obj_arg result_, uint32_t rowNumber,
        uint32_t columnNumber) {
    PGresult* res = unbox_PGresult(result_);
    return lean_mk_string_from_bytes(PQgetvalue(res, rowNumber, columnNumber),
        PQgetlength(res, rowNumber, columnNumber));
}

/* Notifications */

// `Notification` is a structure of three object fields: `channel`, `payload` and `backendPid`.
static lean_object* mk_notification(PGnotify* n) {
    lean_object* r = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(r, 0, mk_string_or_empty(n->relname));
    lean_ctor_set(r, 1, mk_string_or_empty(n->extra));
    lean_ctor_set(r, 2, lean_unsigned_to_nat((unsigned) n->be_pid));
    PQfreemem(n);
    return r;
}

extern "C" lean_obj_res c_PQconsumeInput(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    if (!conn) {
        return closed_error();
    }
    if (!PQconsumeInput(conn)) {
        return make_error(PQerrorMessage(conn));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

// The next notification libpq has already received, if any; this does not read from the socket.
extern "C" lean_obj_res c_PQnotifies(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    if (!conn) {
        return closed_error();
    }
    PGnotify* n = PQnotifies(conn);
    return lean_io_result_mk_ok(n ? mk_some(mk_notification(n)) : mk_none());
}

// Read whatever the server has sent and return all notifications received so far.
extern "C" lean_obj_res c_PQnotifiesAll(b_lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    if (!conn) {
        return closed_error();
    }
    if (!PQconsumeInput(conn)) {
        return make_error(PQerrorMessage(conn));
    }
    lean_object* arr = lean_mk_empty_array();
    while (PGnotify* n = PQnotifies(conn)) {
        arr = lean_array_push(arr, mk_notification(n));
    }
    return lean_io_result_mk_ok(arr);
}

// A monotonic clock in milliseconds, for a wait that survives being interrupted by a signal.
static int64_t now_ms() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t) ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

// Wait up to `timeoutMs` milliseconds for a notification: `poll()` on the connection's socket,
// then `PQconsumeInput` and `PQnotifies`. Returns `none` when the time is up.
extern "C" lean_obj_res c_PQwaitNotify(b_lean_obj_arg conn_, uint32_t timeoutMs) {
    PGconn* conn = unbox_PGconn(conn_);
    if (!conn) {
        return closed_error();
    }
    if (PGnotify* n = PQnotifies(conn)) {
        return lean_io_result_mk_ok(mk_some(mk_notification(n)));
    }
    int sock = PQsocket(conn);
    if (sock < 0) {
        return make_error("the PostgreSQL connection has no open socket");
    }
    int64_t deadline = now_ms() + (int64_t) timeoutMs;
    while (true) {
        int64_t remaining = deadline - now_ms();
        if (remaining < 0) {
            return lean_io_result_mk_ok(mk_none());
        }
        struct pollfd pfd;
        pfd.fd = sock;
        pfd.events = POLLIN;
        pfd.revents = 0;
        int rc = poll(&pfd, 1, (int) remaining);
        if (rc < 0) {
            if (errno == EINTR) {
                continue;
            }
            return make_error(strerror(errno));
        }
        if (rc == 0) {
            return lean_io_result_mk_ok(mk_none());
        }
        if (!PQconsumeInput(conn)) {
            return make_error(PQerrorMessage(conn));
        }
        if (PGnotify* n = PQnotifies(conn)) {
            return lean_io_result_mk_ok(mk_some(mk_notification(n)));
        }
        // Readable, but what arrived was not a notification (a keepalive, say): keep waiting.
    }
}
