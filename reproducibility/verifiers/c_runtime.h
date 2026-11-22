/* Standard C declarations; the optional mode is for a minimal Windows clang
 * distribution with CRT import libraries but without SDK header files.
 * No binary is supplied or trusted by the archive: run_all.py compiles sources.
 */
#ifndef FGST_C_RUNTIME_H
#define FGST_C_RUNTIME_H
#ifdef FGST_NO_C_HEADERS
typedef unsigned long long size_t;
typedef void FILE;
extern FILE *fopen(const char *, const char *);
extern int fclose(FILE *);
extern int fseek(FILE *, long, int);
extern long ftell(FILE *);
extern size_t fread(void *, size_t, size_t, FILE *);
extern void *malloc(size_t);
extern void *calloc(size_t, size_t);
extern void free(void *);
extern int fscanf(FILE *, const char *, ...);
extern int printf(const char *, ...);
extern void exit(int);
#else
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#endif
typedef unsigned long long U64;
typedef long long I64;
typedef size_t SZ;
#endif
