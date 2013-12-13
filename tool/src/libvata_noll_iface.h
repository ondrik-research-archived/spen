/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2012-2014                                               */
/*    LIAFA (University of Paris Diderot and CNRS)                        */
/*    VeriFIT (Brno University of Technology)                             */
/*                                                                        */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 3.                                                */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 3.                  */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

/**
 * Interface to libvata.
 */

#ifndef LIBVATA_NOLL_IFACE_H_
#define LIBVATA_NOLL_IFACE_H_

#ifdef __cplusplus
	extern "C" {
#endif

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */
struct type_noll_ta_t;

typedef struct type_noll_ta_t noll_ta_t;

/* ====================================================================== */
/* Functions */
/* ====================================================================== */

noll_ta_t* vata_create_ta(void);

#ifdef __cplusplus
	} // extern "C"
#endif

#endif /* LIBVATA_NOLL_IFACE_H_ */
