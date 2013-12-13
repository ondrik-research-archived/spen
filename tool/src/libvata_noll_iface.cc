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

// VATA header files
#include <vata/explicit_tree_aut.hh>

#include "libvata_noll_iface.h"

// to catch strange behaviour
#ifndef __cplusplus
	#error "Needs a C++ compiler!"
#endif

typedef VATA::ExplicitTreeAut TreeAut;

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */
typedef struct type_noll_ta_t
{
private:

	TreeAut ta_;

public:

} noll_ta_t;

/* ====================================================================== */
/* Functions */
/* ====================================================================== */

noll_ta_t* vata_create_ta()
{
	noll_ta_t* treeaut = new noll_ta_t;
	if (NULL == treeaut)
	{
		return NULL;
	}





	return treeaut;
}

