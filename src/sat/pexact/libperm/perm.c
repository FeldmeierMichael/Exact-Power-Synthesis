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

#include "perm.h"

/* number of permutations for n members */
size_t perm_count(size_t n_memb) {
	size_t factorial = 1;
	size_t i;
	if (n_memb == 0) return 0;
	for (i = 2; i <= n_memb; i++) factorial *= i;
	return factorial;
}


/* length of a flat array with all permutations of n members */
size_t perm_length(size_t n_memb) {
	return perm_count(n_memb) * n_memb;
}


/* size of permutation array of n members with the given size */
size_t perm_size(size_t n_memb, size_t memb_size) {
	return perm_count(n_memb) * n_memb * memb_size;
}


/* better optimized perm_set() function for memb_size = 1 */
int _perm_set_one(char *f, size_t n_memb, char *d) {
	size_t nm1 = n_memb - 1;
	size_t nm2 = n_memb - 2;
	size_t nm3 = n_memb - 3;
	size_t n2 = n_memb * 2;
	size_t n2m1 = n2 - 1;
	size_t n2m2 = n2 - 2;
	size_t i, fi, factorial, *lookback, *moving;

	/* allocate memory */
	lookback = (size_t *) malloc(sizeof(size_t) * nm2);
	if (lookback == NULL) return PERM_ERR_MALLOC;
	moving = (size_t *) malloc(sizeof(size_t) * nm2);
	if (moving == NULL) {
		free(lookback);
		return PERM_ERR_MALLOC;
	}

	/* initialize lookback and moving arrays */
	for (factorial = n_memb, fi = 2; fi < n_memb; fi++) {
		factorial *= fi;
		lookback[nm1 - fi] = factorial;
	}
	for (i = 0; i < nm2; i++) moving[i] = i;

	/* add the first permutation to dst. swap the last 2 members and add again */
	memcpy(d, f, n_memb);
	memcpy(d + n_memb, f, nm2);
	d[n2m2] = f[nm1];
	d[n2m1] = f[nm2];
	d += n2;

	for (i = nm3;;) {
		if (moving[i] == nm1) {
			moving[i] = i;
			if (i-- == 0) break;
		} else {
			moving[i]++;

			/* set the new permutation to the one at d - lookback[i] */
			memcpy(d, d - lookback[i], n_memb);

			/* swap the ith member with the one at moving[i] */
			d[i] = (d - lookback[i])[moving[i]];
			d[moving[i]] = (d - lookback[i])[i];

			/* swap the last 2 members of the new permutation and add it again */
			memcpy(d + n_memb, d, nm2);
			d[n2m2] = d[nm1];
			d[n2m1] = d[nm2];

			d += n2;
			i = nm3;
		}
	}
	/* free allocated memory and return */
	free(lookback);
	free(moving);
	return PERM_OK;
}


/* create all permutations of n members with the given size starting with first
 * use `perm_size()` to allocate correct amount of memory for dst beforehand */
int perm_set(void *first, size_t n_memb, size_t memb_size, void *dst) {
	char *d, *f;
	if (first == NULL || dst == NULL || n_memb == 0 || memb_size == 0) return PERM_ERR_INPUT;

	d = (char *) dst;
	f = (char *) first;

	if (n_memb == 1) memcpy(d, f, memb_size);
	else if (n_memb == 2) {
		memcpy(d, f, memb_size);
		memcpy(d + memb_size, f + memb_size, memb_size);
		memcpy(d + memb_size * 2, f + memb_size, memb_size);
		memcpy(d + memb_size * 3, f, memb_size);
	} else if (memb_size == 1) return _perm_set_one(f, n_memb, d);
	else {
		size_t nm1 = n_memb - 1;
		size_t nm2 = n_memb - 2;
		size_t nm3 = n_memb - 3;
		size_t n_size = n_memb * memb_size;
		size_t n2_size = n_size * 2;
		size_t nm1_size = n_size - memb_size;
		size_t nm2_size = nm1_size - memb_size;
		size_t n2m1_size = n2_size - memb_size;
		size_t n2m2_size = n2m1_size - memb_size;
		size_t i, fi, factorial, *lookback, *moving;

		/* allocate memory */
		lookback = (size_t *) malloc(sizeof(size_t) * nm2);
		if (lookback == NULL) return PERM_ERR_MALLOC;
		moving = (size_t *) malloc(sizeof(size_t) * nm2);
		if (moving == NULL) {
			free(lookback);
			return PERM_ERR_MALLOC;
		}

		/* initialize lookback and moving arrays */
		for (factorial = n_size, fi = 2; fi < n_memb; fi++) {
			factorial *= fi;
			lookback[nm1 - fi] = factorial;
		}
		for (i = 0; i < nm2; i++) moving[i] = i;

		/* add the first permutation to dst. swap the last 2 members and add again */
		memcpy(d, f, n_size);
		memcpy(d + n_size, f, nm2_size);
		memcpy(d + n2m2_size, f + nm1_size, memb_size);
		memcpy(d + n2m1_size, f + nm2_size, memb_size);
		d += n2_size;

		for (i = nm3;;) {
			if (moving[i] == nm1) {
				moving[i] = i;
				if (i-- == 0) break;
			} else {
				moving[i]++;

				/* set the new permutation to the one at d - lookback[i] */
				memcpy(d, d - lookback[i], n_size);

				/* swap the ith member with the one at moving[i] */
				memcpy(d + i * memb_size, d - lookback[i] + moving[i] * memb_size, memb_size);
				memcpy(d + moving[i] * memb_size, d - lookback[i] + i * memb_size, memb_size);

				/* swap the last 2 members of the new permutation and add it again */
				memcpy(d + n_size, d, nm2_size);
				memcpy(d + n2m2_size, d + nm1_size, memb_size);
				memcpy(d + n2m1_size, d + nm2_size, memb_size);

				d += n2_size;
				i = nm3;
			}
		}
		/* free allocated memory */
		free(lookback);
		free(moving);
	}
	return PERM_OK;
}


/* length of the palindromic superpermutation of n members (https://oeis.org/A007489) */
size_t perm_super_length(size_t n_memb) {
	size_t fact_sum = 1;
	size_t factorial, i;
	if (n_memb == 0) return 0;
	for (i = 2, factorial = 1; i <= n_memb; i++) {
		factorial *= i;
		fact_sum += factorial;
	}
	return fact_sum;
}


/* size of the palindromic superpermutation of n members with the given size */
size_t perm_super_size(size_t n_memb, size_t memb_size) {
	return perm_super_length(n_memb) * memb_size;
}


/* size of an array of permutation indices inside the palindromic superpermutation of n members */
size_t perm_super_indices_size(size_t n_memb, size_t index_size) {
	return perm_count(n_memb) * index_size;
}


/* better optimized perm_set_super() function for memb_size = 1 */
int _perm_set_super_one(char *f, size_t n_memb, char *d) {
	size_t nm1 = n_memb - 1;
	size_t nm2 = n_memb - 2;
	size_t nm3 = n_memb - 3;
	size_t np1 = n_memb + 1;
	size_t n2 = n_memb * 2;
	size_t n2m1 = n2 - 1;
	size_t moving = nm1;
	size_t i, l, *lookback, *count;

	/* allocate memory */
	lookback = (size_t *) malloc(sizeof(size_t) * nm1);
	if (lookback == NULL) return PERM_ERR_MALLOC;
	count = (size_t *) calloc(nm1, sizeof(size_t));
	if (count == NULL) {
		free(lookback);
		return PERM_ERR_MALLOC;
	}

	/* calculate lookback */
	for (l = 0, i = 0; i < nm1; i++) {
		l = (n_memb - i) * (l + 1);
		lookback[i] = l;
	}

	/* add the first permutation to dst */
	memcpy(d, f, n_memb);
	d += n_memb;

	for (i = 0;;) {
		/* if the moving part of the term is at the end of it ... */
		if (moving == nm1 - i) {
			/* add the term with its moving part cut out */
			memcpy(d, d - lookback[i], nm1 - i);

			/* if the remaining term is of length 1, it means we are done */
			if (i == nm2) break;
			
			/* add the first member */
			d[nm1 - i] = f[0];

			/* insert the cut members at index 1 of the remaining part */
			memcpy(d + n_memb - i, d - lookback[i] + nm1 - i, i + 1);
			memcpy(d + np1, d - lookback[i] + 1, nm2 -i);
			d += n2m1 - i;

			moving = i + 1;
			i = 0;
		}

		if (count[i] == nm3 - i) count[i++] = 0;
		else {
			/* shift the moving part of the term one position to the right and add it to dst */
			memcpy(d, d - lookback[i], moving);
			d[moving] = (d - lookback[i])[moving + i + 1];
			memcpy(d + moving + 1, d - lookback[i] + moving, i + 1);
			memcpy(d + moving + i + 2, d - lookback[i] + moving + i + 2, nm2 - moving - i);
			d += n_memb;

			moving += i + 1;
			count[i]++;
			i = 0;
		}
	}
	/* free allocated memory and return */
	free(lookback);
	free(count);
	return PERM_OK;
}

/* create the palindromic superpermutation of n members with the given size starting with first
 * use `perm_super_size()` to allocate correct amount of memory for dst beforehand */
int perm_set_super(void *first, size_t n_memb, size_t memb_size, void *dst) {
	char *d, *f;
	size_t nm1 = n_memb - 1;
	size_t nm2 = n_memb - 2;
	size_t nm3 = n_memb - 3;
	size_t moving = nm1;
	size_t memb2_size = memb_size * 2;
	size_t n_size = n_memb * memb_size;
	size_t n2_size = n_size * 2;
	size_t np1_size = n_size + memb_size;
	size_t nm1_size = n_size - memb_size;
	size_t nm2_size = nm1_size - memb_size;
	size_t n2m1_size = n2_size - memb_size;
	size_t i, l, *lookback, *count;

	if (first == NULL || dst == NULL || n_size == 0) return PERM_ERR_INPUT;

	f = (char *) first;
	d = (char *) dst;

	if (n_memb == 1) {
		memcpy(d, f, memb_size);
		return PERM_OK;
	}

	if (memb_size == 1) return _perm_set_super_one(f, n_memb, d);

	/* allocate memory */
	lookback = (size_t *) malloc(sizeof(size_t) * nm1);
	if (lookback == NULL) return PERM_ERR_MALLOC;
	count = (size_t *) calloc(nm2, sizeof(size_t));
	if (count == NULL) {
		free(lookback);
		return PERM_ERR_MALLOC;
	}

	/* calculate lookback */
	for (l = 0, i = 0; i < nm1; i++) {
		l = (n_memb - i) * (l + memb_size);
		lookback[i] = l;
	}

	/* add the first permutation to dst */
	memcpy(d, f, n_size);
	d += n_size;

	for (i = 0;;) {
		/* if the moving part of the term is at the end of it ... */
		if (moving == nm1 - i) {
			size_t i_size = i * memb_size;

			/* add the term with its moving part cut out */
			memcpy(d, d - lookback[i], nm1_size - i_size);

			/* if the remaining term is of length 1, it means we are done */
			if (i == nm2) break;
			
			/* add the first member */
			memcpy(d + nm1_size - i_size, f, memb_size);

			/* insert the cut members at index 1 of the remaining part */
			memcpy(d + n_size - i_size, d - lookback[i] + nm1_size - i_size, i_size + memb_size);
			memcpy(d + np1_size, d - lookback[i] + memb_size, nm2_size - i_size);
			d += n2m1_size - i_size;

			moving = i + 1;
			i = 0;
		}

		if (count[i] == nm3 - i) count[i++] = 0;
		else {
			size_t i_size = i * memb_size;
			size_t m_size = moving * memb_size;

			/* shift the moving part of the term one position to the right and add it to dst */
			memcpy(d, d - lookback[i], m_size);
			memcpy(d + m_size, d - lookback[i] + m_size + i_size + memb_size, memb_size);
			memcpy(d + m_size + memb_size, d - lookback[i] + m_size, i_size + memb_size);
			memcpy(d + m_size + i_size + memb2_size, d - lookback[i] + m_size + i_size + memb2_size,
					nm2_size - m_size - i_size);
			d += n_size;

			moving += i + 1;
			count[i]++;
			i = 0;
		}
	}
	/* free allocated memory and return */
	free(lookback);
	free(count);
	return PERM_OK;
}

/* create permutation indices for the palindromic superpermutation of n members
 * use `perm_super_indices_size()` to allocate correct amount of memory for dst beforehand */
#define _PERM_SET_SUPER_INDICES(i_type, max) \
	if (dst == NULL || n_memb == 0) return PERM_ERR_INPUT; \
	if (n_memb < 3) { \
		i_type i; \
		for (i = 0; i < n_memb; i++) dst[i] = i; \
	} else { \
		/* calculate maximum dst index and permutation index */ \
		size_t s_max_di = perm_super_length(n_memb) - n_memb; \
		size_t s_max_pi = perm_count(n_memb) - 1; \
		i_type i, nm1, nm2, di, pi, max_di, max_pi, *count; \
		/* check if index of all permutations can fit inside i_type */ \
		if (s_max_pi + 1 > max) return PERM_ERR_INDEX_TYPE; \
		/* cast these to index type to suppress conversion warnings */ \
		max_di = (i_type) s_max_di; \
		max_pi = (i_type) s_max_pi; \
		/* allocate memory for count */ \
		nm1 = (i_type) (n_memb - 1); \
		nm2 = (i_type) (n_memb - 2); \
		count = (i_type *) calloc(nm2, sizeof(i_type)); \
		if (count == NULL) return PERM_ERR_MALLOC; \
		/* set indices */ \
		for (i = 0, di = 0, pi = 0;;) { \
			if (count[i] == nm1 - i) { \
				count[i++] = 0; \
				if (i == nm2) { \
					dst[max_pi - pi] = max_di - di; \
					dst[pi] = di; \
					break; \
				} \
			} else { \
				dst[max_pi - pi] = max_di - di; \
				dst[pi++] = di; \
				di += (i_type) (i + 1); \
				count[i]++; \
				i = 0; \
			} \
		} \
		free(count); \
	} \
	return PERM_OK


int perm_set_super_indices(size_t n_memb, size_t *dst) {
	/* no need to include stdint.h for SIZE_MAX, the check is never going to be false for size_t anyway */
	_PERM_SET_SUPER_INDICES(size_t, s_max_pi + 1);
}

int perm_set_super_indices_uchar(size_t n_memb, unsigned char *dst) {
	_PERM_SET_SUPER_INDICES(unsigned char, UCHAR_MAX);
}

int perm_set_super_indices_ushort(size_t n_memb, unsigned short *dst) {
	_PERM_SET_SUPER_INDICES(unsigned short, USHRT_MAX);
}

int perm_set_super_indices_uint(size_t n_memb, unsigned int *dst) {
	_PERM_SET_SUPER_INDICES(unsigned int, UINT_MAX);
}

int perm_set_super_indices_ulong(size_t n_memb, unsigned long *dst) {
	_PERM_SET_SUPER_INDICES(unsigned long, ULONG_MAX);
}
