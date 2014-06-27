/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure - the data structure for a tree               */
/*                                                                        */
/*  Copyright (C) 2013                                                    */
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

#ifndef _NOLL_TREE_H_
#define _NOLL_TREE_H_

struct noll_tree_node_t;

NOLL_VECTOR_DECLARE (noll_tree_node_array, noll_tree_node_t *);

/**
 * @brief  A tree node
 */
typedef struct noll_tree_node_s
{
	/// The symbol in the node
	const noll_ta_symbol_t* symbol;

	/// Children of the node (ordered)
	noll_tree_node_array* children;
} noll_tree_node_t;


/// The tree - now an alias for the root node
typedef noll_tree_node_t noll_tree_t;


#endif /* _NOLL_TREE_H_ */
