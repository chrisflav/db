/*
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
*/
#include <lean/lean.h>
#include <libpq-fe.h>

#define l_arg b_lean_obj_arg
#define l_res lean_obj_res

static lean_external_class* g_PGconn_external_class = NULL;
static lean_external_class* g_PGresult_external_class = NULL;

inline static void PGconn_finalizer(void* conn_ptr) {
    PGconn* conn = (PGconn*) conn_ptr;
    if (conn) {
        PQfinish(conn);
    }
}

inline static void PGresult_finalizer(void* result) {}

inline static void noop_foreach(void* mod, b_lean_obj_arg fn) {}

// Initialize external classes
static void initialize_classes() {
    if (!g_PGconn_external_class) {
        g_PGconn_external_class = lean_register_external_class(PGconn_finalizer, noop_foreach);
    }
    if (!g_PGresult_external_class) {
        g_PGresult_external_class = lean_register_external_class(NULL, noop_foreach);
    }
}

inline static lean_object* box_PGconn(PGconn* conn) {
    return lean_alloc_external(g_PGconn_external_class, conn);
}

inline static lean_object* box_PGresult(PGresult* result) {
    return lean_alloc_external(g_PGresult_external_class, result);
}

inline static PGconn* unbox_PGconn(lean_object* o) {
    return (PGconn*) (lean_get_external_data(o));
}

inline static PGresult* unbox_PGresult(lean_object* o) {
    return (PGresult*) (lean_get_external_data(o));
}

inline static lean_obj_res make_error(const char* err_msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(err_msg)));
}

extern "C" lean_obj_res lean_PGconn_mk(uint64_t b) {
    // Initialize external classes if not already done
    // initialize_classes();

    // This function shouldn't really create a PGconn directly
    // Instead return a null connection that needs to be connected
    return lean_io_result_mk_ok(box_PGconn(NULL));
}

extern "C" lean_obj_res c_PQconnectdb(lean_obj_arg s_) {
    // Initialize external classes if not already done
    initialize_classes();

    const char* s = lean_string_cstr(s_);
    PGconn* conn = PQconnectdb(s);
    if (!conn) {
        return make_error("Failed to allocate PostgreSQL connection");
    }
    return lean_io_result_mk_ok(box_PGconn(conn));
}

extern "C" uint8_t c_PQstatus(lean_obj_arg conn_) {
    PGconn* conn = unbox_PGconn(conn_);
    return PQstatus(conn);
}

extern "C" lean_obj_res c_PQexec(lean_obj_arg conn_, lean_obj_arg query_) {
    PGconn* conn = unbox_PGconn(conn_);
    const char *query = lean_string_cstr(query_);

    PGresult *res;
    res = PQexec(conn, query);
    return lean_io_result_mk_ok(box_PGresult(res));
}

extern "C" lean_obj_res c_PQresultStatus(lean_obj_arg result_) {
    char* status = PQresStatus(PQresultStatus(unbox_PGresult(result_)));
    return lean_mk_string(status);
}

extern "C" uint32_t c_PQntuples(lean_obj_arg result_) {
    return PQntuples(unbox_PGresult(result_));
}

extern "C" uint32_t c_PQnfields(lean_obj_arg result_) {
    return PQnfields(unbox_PGresult(result_));
}

extern "C" lean_obj_res c_PQfname(lean_obj_arg result_, uint32_t columnNumber) {
    return lean_mk_string(PQfname(unbox_PGresult(result_), columnNumber));
}

extern "C" uint32_t c_PQftable(lean_obj_arg result_, uint32_t columnNumber) {
    return PQftable(unbox_PGresult(result_), columnNumber);
}

extern "C" int32_t c_PQfnumber(lean_obj_arg result_, lean_obj_arg columnName_) {
    return PQfnumber(unbox_PGresult(result_), lean_string_cstr(columnName_));
}

extern "C" uint32_t c_PQgetisnull(lean_obj_arg result_, uint32_t rowNumber, uint32_t columnNumber) {
    return PQgetisnull(unbox_PGresult(result_), rowNumber, columnNumber);
}

extern "C" uint32_t c_PQgetlength(lean_obj_arg result_, uint32_t rowNumber, uint32_t columnNumber) {
    return PQgetlength(unbox_PGresult(result_), rowNumber, columnNumber);
}

extern "C" lean_obj_res c_PQgetvalue(lean_obj_arg result_, uint32_t rowNumber, uint32_t columnNumber) {
    return lean_mk_string(PQgetvalue(unbox_PGresult(result_), rowNumber, columnNumber));
}
