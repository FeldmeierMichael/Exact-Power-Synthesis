/* MIT License
Copyright (c) 2022 Arash Rohani

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE. */

#ifndef _PERM_H
#define _PERM_H

#define PERM_VERSION_MAJOR 1
#define PERM_VERSION_MINOR 0
#define PERM_VERSION_PATCH 0

#include <string.h> /* memcpy */
#include <stdlib.h> /* malloc, calloc, free */
#include <limits.h> /* UCHAR_MAX, USHRT_MAX, UINT_MAX, ULONG_MAX */

/* function return values */
enum {
	PERM_OK = 0,         /* no errors */
	PERM_ERR_INPUT,      /* unacceptable function input */
	PERM_ERR_MALLOC,     /* malloc failure */
	PERM_ERR_INDEX_TYPE  /* index type is too small */
};


#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

/* number of permutations for n members */
size_t perm_count(size_t n_memb);

/* length of a flat array with all permutations of n members */
size_t perm_length(size_t n_memb);

/* size of permutation array of n members with the given size */
size_t perm_size(size_t n_memb, size_t memb_size);

/* create all permutations of n members with the given size starting with first */
int perm_set(void *first, size_t n_memb, size_t memb_size, void *dst);

/* length of the palindromic superpermutation of n members (https://oeis.org/A007489) */
size_t perm_super_length(size_t n_memb);

/* size of the palindromic superpermutation of n members with the given size */
size_t perm_super_size(size_t n_memb, size_t memb_size);

/* size of an array of permutation indices inside the palindromic superpermutation of n members */
size_t perm_super_indices_size(size_t n_memb, size_t index_size);

/* create the palindromic superpermutation of n members with the given size starting with first */
int perm_set_super(void *first, size_t n_memb, size_t memb_size, void *dst);

/* create permutation indices for the palindromic superpermutation of n members */
int perm_set_super_indices       (size_t n_memb, size_t         *dst);
int perm_set_super_indices_uchar (size_t n_memb, unsigned char  *dst);
int perm_set_super_indices_ushort(size_t n_memb, unsigned short *dst);
int perm_set_super_indices_uint  (size_t n_memb, unsigned int   *dst);
int perm_set_super_indices_ulong (size_t n_memb, unsigned long  *dst);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif /* _PERM_H */
