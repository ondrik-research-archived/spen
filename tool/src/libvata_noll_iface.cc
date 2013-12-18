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
#include <vata/serialization/timbuk_serializer.hh>

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
	TreeAut ta;
} noll_ta_t;

/* ====================================================================== */
/* Functions */
/* ====================================================================== */

vata_ta_t* vata_create_ta()
{
	vata_ta_t* ta = new vata_ta_t;

	VATA::ExplicitTreeAut::AlphabetType directAlph(
		new VATA::ExplicitTreeAut::DirectAlphabet);
	ta->ta.SetAlphabet(directAlph);

	return ta;
}

void vata_free_ta(
	vata_ta_t*       ta)
{
	delete ta;
}

void vata_set_state_root(
	vata_ta_t*          ta,
	vata_state_t        state)
{
	// check whether the input is sane
	assert(NULL != ta);

	ta->ta.SetStateFinal(state);
}

void vata_add_transition(
	vata_ta_t*              ta,
	vata_state_t            parent,
	const vata_symbol_t*    symbol,
	const vata_state_t*     children,
	size_t                  numChildren)
{
	// check that the input is sane
	assert(NULL != ta);
	assert((numChildren == 0) || (NULL != children));

	TreeAut::StateTuple tupChildren(children, children + numChildren);
	uintptr_t vataSymbol = reinterpret_cast<uintptr_t>(symbol);

	ta->ta.AddTransition(tupChildren, vataSymbol, parent);
}


void vata_print_ta(
	const vata_ta_t*        ta)
{
	// check that the input is sane
	assert(NULL != ta);

	std::cout << "TreeAutomaton:  <*(((><       <-- this is a fish, not a TA!\n";

	VATA::Serialization::TimbukSerializer serializer;
	std::cout << ta->ta.DumpToString(serializer);
}
