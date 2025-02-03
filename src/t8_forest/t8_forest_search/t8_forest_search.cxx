/*
This file is part of t8code.
t8code is a C library to manage a collection (a forest) of multiple
connected adaptive space-trees of general element classes in parallel.

Copyright (C) 2024 the developers

t8code is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

t8code is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with t8code; if not, write to the Free Software Foundation, Inc.,
51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
*/

#include "t8_forest/t8_forest_search/t8_forest_search.hxx"
#include "t8_forest/t8_forest_search/t8_forest_search.h"
#include <t8_forest/t8_forest_iterate.h>
#include <t8_forest/t8_forest_types.h>
#include <t8_forest/t8_forest_general.h>
#include <t8_schemes/t8_scheme.hxx>
#include <t8_cmesh/t8_cmesh_offset.h>

void
t8_search_base::search_recursion (const t8_locidx_t ltreeid, t8_element_t *element, const t8_scheme *ts,
                                  t8_element_array_t *leaf_elements, const t8_locidx_t tree_lindex_of_first_leaf)
{
  /* Assertions to check for necessary requirements */
  /* The forest must be committed */
  T8_ASSERT (t8_forest_is_committed (this->forest));
  /* The tree must be local */
  T8_ASSERT (0 <= ltreeid && ltreeid < t8_forest_get_num_local_trees (this->forest));

  const size_t elem_count = t8_element_array_get_count (leaf_elements);
  if (elem_count == 0) {
    /* There are no leaves left, so we have nothing to do */
    return;
  }

  if (this->stop_due_to_queries ()) {
    return;
  }

  const t8_eclass_t eclass = t8_forest_get_eclass (this->forest, ltreeid);

  bool is_leaf = false;
  if (elem_count == 1) {
    /* There is only one leaf left, we check whether it is the same as element and if so call the callback function */
    const t8_element_t *leaf = t8_element_array_index_locidx (leaf_elements, 0);

    SC_CHECK_ABORT (ts->element_get_level (eclass, element) <= ts->element_get_level (eclass, leaf),
                    "Search: element level greater than leaf level\n");
    if (ts->element_get_level (eclass, element) == ts->element_get_level (eclass, leaf)) {
      T8_ASSERT (t8_forest_element_is_leaf (this->forest, leaf, ltreeid));
      T8_ASSERT (ts->element_is_equal (eclass, element, leaf));
      /* The element is the leaf */
      is_leaf = true;
    }
  }
  /* Call the callback function for the element */
  const bool ret = check_element (ltreeid, element, is_leaf, leaf_elements, tree_lindex_of_first_leaf);

  if (!ret) {
    /* The function returned false. We abort the recursion */
    return;
  }
  std::vector<size_t> new_active_queries;
  this->check_queries (new_active_queries, ltreeid, element, is_leaf, leaf_elements, tree_lindex_of_first_leaf);

  if (is_leaf) {
    return;
  }

  /* Enter the recursion (the element is definitely not a leaf at this point) */
  /* We compute all children of E, compute their leaf arrays and call search_recursion */
  /* allocate the memory to store the children */
  const int num_children = ts->element_get_num_children (eclass, element);
  t8_element_t **children = T8_ALLOC (t8_element_t *, num_children);
  ts->element_new (eclass, num_children, children);
  /* Memory for the indices that split the leaf_elements array */
  size_t *split_offsets = T8_ALLOC (size_t, num_children + 1);
  /* Compute the children */
  ts->element_get_children (eclass, element, num_children, children);
  /* Split the leaves array in portions belonging to the children of element */
  t8_forest_split_array (element, leaf_elements, split_offsets);
  for (int ichild = 0; ichild < num_children; ichild++) {
    /* Check if there are any leaf elements for this child */
    const size_t indexa = split_offsets[ichild];     /* first leaf of this child */
    const size_t indexb = split_offsets[ichild + 1]; /* first leaf of next child */
    if (indexa < indexb) {
      t8_element_array_t child_leaves;
      /* There exist leaves of this child in leaf_elements,
       * we construct an array of these leaves */
      t8_element_array_init_view (&child_leaves, leaf_elements, indexa, indexb - indexa);
      /* Enter the recursion */
      search_recursion (ltreeid, children[ichild], ts, &child_leaves, indexa + tree_lindex_of_first_leaf);
      update_queries (new_active_queries);
    }
  }

  /* clean-up */
  ts->element_destroy (eclass, num_children, children);
  T8_FREE (children);
  T8_FREE (split_offsets);
}

void
t8_search_base::search_tree (const t8_locidx_t ltreeid)
{
  const t8_eclass_t eclass = t8_forest_get_eclass (this->forest, ltreeid);
  const t8_scheme *ts = t8_forest_get_scheme (this->forest);
  t8_element_array_t *leaf_elements = t8_forest_tree_get_leaves (this->forest, ltreeid);

  /* assert for empty tree */
  T8_ASSERT (t8_element_array_get_count (leaf_elements) >= 0);
  /* Get the first and last leaf of this tree */
  const t8_element_t *first_el = t8_element_array_index_locidx (leaf_elements, 0);
  const t8_element_t *last_el
    = t8_element_array_index_locidx (leaf_elements, t8_element_array_get_count (leaf_elements) - 1);
  /* Compute their nearest common ancestor */
  t8_element_t *nca;
  ts->element_new (eclass, 1, &nca);
  ts->element_get_nca (eclass, first_el, last_el, nca);

  /* Start the top-down search */
  this->search_recursion (ltreeid, nca, ts, leaf_elements, 0);

  ts->element_destroy (eclass, 1, &nca);
}

void
t8_search_base::do_search ()
{
  T8_ASSERT (t8_forest_is_committed (forest));
  const t8_locidx_t num_local_trees = t8_forest_get_num_local_trees (this->forest);
  for (t8_locidx_t itree = 0; itree < num_local_trees; itree++) {
    this->search_tree (itree);
  }
}

/* This function is called in sc_split_array to obtain the tree offset for a
 * given process with rank index. */
static size_t
t8_forest_determine_tree (sc_array_t *tree_offsets, size_t index, void *data)
{
  T8_ASSERT (data != NULL);
  t8_gloidx_t *offset = (t8_gloidx_t *) data;
  t8_gloidx_t tree_id = t8_offset_first ((int) index, offset);

  /* to obtain a monotonous array we need to decrement tree_id on empty processes */
  if (tree_id > 0 && index < tree_offsets->elem_count - 1 && t8_offset_empty ((int) index, offset)) {
    tree_id--;
  }
  return (size_t) tree_id;
}

/* Transforms a shmem array into an sc_array_t, which can be passed to
 * sc_split_array. */
static sc_array_t *
t8_forest_get_sc_array_view (t8_shmem_array_t shmem_array)
{
  return sc_array_new_data ((t8_gloidx_t *) t8_shmem_array_get_array (shmem_array),
                            t8_shmem_array_get_elem_size (shmem_array), t8_shmem_array_get_elem_count (shmem_array));
}

void
t8_partition_search_base::do_search ()
{
  T8_ASSERT (t8_forest_is_committed (forest));
  T8_ASSERT (!t8_cmesh_is_partitioned (t8_forest_get_cmesh (forest)));
  T8_ASSERT (forest->tree_offsets != NULL);

  /* to get process offsets of each tree we need tree offsets of each process */
  const t8_locidx_t num_global_trees = t8_forest_get_num_global_trees (forest);
  int num_procs = forest->mpisize;
  sc_array_t *tree_offsets_view = t8_forest_get_sc_array_view (forest->tree_offsets);
  t8_gloidx_t *offset = (t8_gloidx_t *) tree_offsets_view->array;
  sc_array_t *process_offsets = sc_array_new_size (sizeof (size_t), num_global_trees + 2);

  /* split processors into tree-wise sections, going one beyond */
  sc_array_split (tree_offsets_view, process_offsets, num_global_trees + 1, t8_forest_determine_tree, offset);
  T8_ASSERT (*(size_t *) sc_array_index (process_offsets, (size_t) num_global_trees + 1) == (size_t) num_procs + 1);
  T8_ASSERT (*(size_t *) sc_array_index (process_offsets, (size_t) num_global_trees) == (size_t) num_procs);
  T8_ASSERT (*(size_t *) sc_array_index (process_offsets, 0) == 0);

  sc_array_t *global_first_desc_view = t8_forest_get_sc_array_view (forest->global_first_desc);
  int pfirst, plast, pnext;
  t8_locidx_t itree;
  for (pfirst = 0, itree = 0; itree < num_global_trees; pfirst = pnext, itree++) {
    pnext = *(int *) sc_array_index (process_offsets, itree + 1);
    T8_ASSERT (pfirst <= pnext && pnext <= num_procs);

    /* fix the last processor in the tree, which is known at this point */
    T8_ASSERT (pnext > 0);
    plast = pnext - 1;

    while (t8_offset_empty (plast, offset)) {
      --plast;
      T8_ASSERT (t8_forest_determine_tree (tree_offsets_view, plast, offset) == (size_t) itree);
    }

    /* now check multiple cases for the beginning processor */
    if (pfirst < pnext) {
      /* at least one processor starts in this tree */

      if (t8_shmem_array_get_gloidx (forest->tree_offsets, pfirst) >= 0) {
        /* pfirst starts at the tree's first descendant but may be empty */
        while (t8_offset_empty (pfirst, offset)) {
          ++pfirst;
          T8_ASSERT (t8_forest_determine_tree (tree_offsets_view, pfirst, offset) == (size_t) itree);
        }
      }
      else {
        /* there must be exactly one processor before us in this tree */
        --pfirst;
        T8_ASSERT (t8_forest_determine_tree (tree_offsets_view, pfirst, offset) < (size_t) itree);
      }
    }
    else {
      /* this whole tree is owned by one processor */
      pfirst = plast;
    }

    /* we should have found tight bounds on processors for this tree */
    T8_ASSERT (pfirst <= plast && plast < num_procs);

    /* we know these are non-negative; check before casting to unsigned */
    T8_ASSERT (plast >= 0 && pnext >= 0 && num_procs >= 0);

    /* These casts remove compiler warnings due to the assumption of the
     * compiler under -O3 that there cannot happen a signed overflow.
     */
    T8_ASSERT ((unsigned) plast <= (unsigned) pnext && (unsigned) pnext <= (unsigned) num_procs);
    T8_ASSERT (t8_forest_determine_tree (tree_offsets_view, plast, offset) <= (size_t) itree);

    /* Todo: go into recursion for this tree */
  }

  sc_array_destroy (global_first_desc_view);
  sc_array_destroy (process_offsets);
  sc_array_destroy (tree_offsets_view);
}

/* #################### t8_forest_search c interface #################### */
T8_EXTERN_C_BEGIN ();

struct t8_forest_c_search
{
  t8_search<void *> *cpp_search;
};

void
t8_forest_init_search (t8_forest_search_c_wrapper search, t8_search_element_callback_c_wrapper element_callback,
                       const t8_forest_t forest)
{
  T8_ASSERT (search != NULL);
  T8_ASSERT (element_callback != NULL);
  search->cpp_search = new t8_search<void *> (element_callback, forest);
}

void
t8_forest_search_update_forest (t8_forest_search_c_wrapper search, const t8_forest_t forest)
{
  T8_ASSERT (search != NULL);
  T8_ASSERT (forest != NULL);
  search->cpp_search->update_forest (forest);
}

void
t8_forest_search_update_user_data (t8_forest_search_c_wrapper search, void *udata)
{
  T8_ASSERT (search != NULL);
  T8_ASSERT (udata != NULL);
  search->cpp_search->update_user_data (&udata);
}

void
t8_forest_search_do_search (t8_forest_search_c_wrapper search)
{
  T8_ASSERT (search != NULL);
  search->cpp_search->do_search ();
}

void
t8_forest_search_destroy (t8_forest_search_c_wrapper search)
{
  T8_ASSERT (search != NULL);
  delete search->cpp_search;
  search->cpp_search = NULL;
}

struct t8_forest_search_with_queries
{
  t8_search_with_queries<void *, void *> *cpp_search;
};

void
t8_forest_init_search_with_queries (t8_forest_search_with_queries_c_wrapper search_with_queries,
                                    t8_search_element_callback_c_wrapper element_callback,
                                    t8_search_queries_callback_c_wrapper queries_callback, void **queries,
                                    const size_t num_queries, const t8_forest_t forest)
{
  T8_ASSERT (search_with_queries != NULL);
  T8_ASSERT (element_callback != NULL);
  T8_ASSERT (queries_callback != NULL);
  T8_ASSERT (queries != NULL);
  T8_ASSERT (forest != NULL);

  std::vector<void *> queries_vector = std::vector<void *> (queries, queries + num_queries);

  search_with_queries->cpp_search
    = new t8_search_with_queries<void *, void *> (element_callback, queries_callback, queries_vector, forest);
}

void
t8_forest_search_with_queries_update_forest (t8_forest_search_with_queries_c_wrapper search_with_queries,
                                             const t8_forest_t forest)
{
  T8_ASSERT (search_with_queries != NULL);
  T8_ASSERT (forest != NULL);
  search_with_queries->cpp_search->update_forest (forest);
}

void
t8_forest_search_with_queries_update_user_data (t8_forest_search_with_queries_c_wrapper search_with_queries,
                                                void *udata)
{
  T8_ASSERT (search_with_queries != NULL);
  T8_ASSERT (udata != NULL);
  search_with_queries->cpp_search->update_user_data (&udata);
}

void
t8_forest_search_with_queries_update_queries (t8_forest_search_with_queries_c_wrapper search_with_queries,
                                              void **queries, const size_t num_queries)
{
  T8_ASSERT (search_with_queries != NULL);
  T8_ASSERT (queries != NULL);

  std::vector<void *> queries_vector = std::vector<void *> (queries, queries + num_queries);

  search_with_queries->cpp_search->update_queries (queries_vector);
}

void
t8_forest_search_with_queries_do_search (t8_forest_search_with_queries_c_wrapper search)
{
  T8_ASSERT (search != NULL);
  search->cpp_search->do_search ();
}

void
t8_forest_search_with_queries_destroy (t8_forest_search_with_queries_c_wrapper search)
{
  T8_ASSERT (search != NULL);
  delete search->cpp_search;
  search->cpp_search = NULL;
}

struct t8_forest_search_with_batched_queries
{
  t8_search_with_batched_queries<void *, void *> *cpp_search;
  t8_search_batched_queries_callback_c_wrapper queries_callback;

  void
  wrapped_queries_callback (const t8_forest_t forest, const t8_locidx_t ltreeid, const t8_element_t *element,
                            const bool is_leaf, const t8_element_array_t *leaf_elements,
                            const t8_locidx_t tree_leaf_index, const std::vector<void *> &queries,
                            const std::vector<size_t> &active_query_indices, std::vector<bool> &query_matches,
                            void *user_data)
  {
    std::vector<int> query_matches_int (query_matches.size ());
    queries_callback (forest, ltreeid, element, is_leaf, leaf_elements, tree_leaf_index, queries.data (),
                      active_query_indices.data (), query_matches_int.data (), user_data);
    std::transform (query_matches_int.begin (), query_matches_int.end (), query_matches.begin (),
                    [] (int val) { return static_cast<bool> (val); });
  }
};

void
t8_forest_init_search_with_batched_queries (t8_forest_search_with_batched_queries_c_wrapper search_with_queries,
                                            t8_search_element_callback_c_wrapper element_callback,
                                            t8_search_batched_queries_callback_c_wrapper queries_callback,
                                            void **queries, const size_t num_queries, const t8_forest_t forest)
{
  T8_ASSERT (search_with_queries != NULL);
  T8_ASSERT (element_callback != NULL);
  T8_ASSERT (queries_callback != NULL);
  T8_ASSERT (queries != NULL);
  T8_ASSERT (forest != NULL);

  std::vector<void *> queries_vector = std::vector<void *> (queries, queries + num_queries);

  search_with_queries->queries_callback = queries_callback;

  search_with_queries->cpp_search = new t8_search_with_batched_queries<void *, void *> (
    element_callback,
    [&search_with_queries] (
      const t8_forest_t forest, const t8_locidx_t ltreeid, const t8_element_t *element, const bool is_leaf,
      const t8_element_array_t *leaf_elements, const t8_locidx_t tree_leaf_index, const std::vector<void *> &queries,
      const std::vector<size_t> &active_query_indices, std::vector<bool> &query_matches, void *user_data) {
      search_with_queries->wrapped_queries_callback (forest, ltreeid, element, is_leaf, leaf_elements, tree_leaf_index,
                                                     queries, active_query_indices, query_matches, user_data);
    },
    queries_vector, forest);
}

void
t8_forest_search_with_batched_queries_update_forest (
  t8_forest_search_with_batched_queries_c_wrapper search_with_queries, const t8_forest_t forest)
{
  T8_ASSERT (search_with_queries != NULL);
  T8_ASSERT (forest != NULL);
  search_with_queries->cpp_search->update_forest (forest);
}

void
t8_forest_search_with_batched_queries_update_user_data (
  t8_forest_search_with_batched_queries_c_wrapper search_with_queries, void *udata)
{
  T8_ASSERT (search_with_queries != NULL);
  T8_ASSERT (udata != NULL);
  search_with_queries->cpp_search->update_user_data (&udata);
}
void
t8_forest_search_with_batched_queries_update_queries (
  t8_forest_search_with_batched_queries_c_wrapper search_with_queries, void **queries, const size_t num_queries)
{
  T8_ASSERT (search_with_queries != NULL);
  T8_ASSERT (queries != NULL);

  std::vector<void *> queries_vector = std::vector<void *> (queries, queries + num_queries);

  search_with_queries->cpp_search->update_queries (queries_vector);
}
void
t8_forest_search_with_batched_queries_destroy (t8_forest_search_with_batched_queries_c_wrapper search)
{
  T8_ASSERT (search != NULL);
  delete search->cpp_search;
  search->cpp_search = NULL;
}

void
t8_forest_search_with_batched_queries_do_search (t8_forest_search_with_batched_queries_c_wrapper search)
{
  T8_ASSERT (search != NULL);
  search->cpp_search->do_search ();
}
T8_EXTERN_C_END ();
