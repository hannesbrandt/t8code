/*
  This file is part of t8code.
  t8code is a C library to manage a collection (a forest) of multiple
  connected adaptive space-trees of general element classes in parallel.

  Copyright (C) 2015 the developers

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

/** \file t8_geometry_bspline.hxx
 * TODO: Add description
 */

#ifndef T8_GEOMETRY_BSPLINE_HXX
#define T8_GEOMETRY_BSPLINE_HXX

#include <t8.h>
#include <t8_geometry/t8_geometry_base.hxx>

#include <gp_Pnt.hxx>
#include <Geom_BSplineCurve.hxx>
#include <Geom_BSplineSurface.hxx>

/**
 * Definition of an bspline geometry function.
 * This function maps reference coordinates to physical
 * coordinates.
 * \param [in]  cmesh       The cmesh.
 * \param [in]  gtreeid     The global tree (of the cmesh) in which the reference point is.
 * \param [in]  ref_coords  Array of \a dimension many entries, specifying a point in [0,1]^dimension.
 * \param [out] out_coords  The mapped coordinates in physical space of \a ref_coords.
 * \param [in]  tree_data   The data of the current tree as loaded by a \ref t8_geom_load_tree_data_fn.
 * \param [in]  bspline     The unterlying bspline geometry for the cell.
 */
typedef void        (*t8_geom_bspline_fn) (t8_cmesh_t cmesh,
                                            t8_gloidx_t gtreeid,
                                            const double *ref_coords,
                                            double out_coords[3],
                                            const void *tree_data,
                                            const Handle_Geom_BSplineSurface bspline);

/* TODO: Document. */
typedef void        (*t8_geom_load_tree_data_fn) (t8_cmesh_t cmesh,
                                                  t8_gloidx_t gtreeid,
                                                  const void **tree_data);

struct t8_geometry_bspline:public t8_geometry
{
public:

  /**
   * Constructor with analytical and jacobian functions.
   * \param [in] dimension  The dimension of this geometry.
   * \param [in] name       The name to give this geometry.
   * \param [in] load_tree_data The function that is used to load a tree's data.
   */
  t8_geometry_bspline (int dimension, const char *name,
                        t8_geom_load_tree_data_fn load_tree_data,
                        const Handle_Geom_BSplineSurface bspline_in);

  /** The destructor. 
   * Clears the allocated memory.
   */
                      virtual ~ t8_geometry_bspline ()
  {
    /* Nothing to do */
  }

  /**
   * Map a point in the reference space $$[0,1]^dimension$$ to $$\mathbb R^3$$
   * \param [in]  cmesh      The cmesh in which the point lies.
   * \param [in]  gtreeid    The glocal tree (of the cmesh) in which the reference point is.
   * \param [in]  ref_coords  Array of \a dimension many entries, specifying a point in [0,1]^dimension.
   * \param [out] out_coords  The mapped coordinates in physical space of \a ref_coords.
   * \note Since this is the identity geometry, \a out_coords will be equal to \a ref_coords.
   */
  virtual void        t8_geom_evaluate (t8_cmesh_t cmesh,
                                        t8_gloidx_t gtreeid,
                                        const double *ref_coords,
                                        double out_coords[3]) const;

  /**
   * Compute the jacobian of the \a t8_geom_evaluate map at a point in the reference space $$[0,1]^dimension$$.
   * \param [in]  cmesh      The cmesh in which the point lies.
   * \param [in]  gtreeid    The glocal tree (of the cmesh) in which the reference point is.
   * \param [in]  ref_coords  Array of \a dimension many entries, specifying a point in [0,1]^dimension.
   * \param [out] jacobian    The jacobian at \a ref_coords. Array of size dimension x 3. Indices 3*i, 3*i+1, 3*i+2
   *                          correspond to the i-th column of the jacobian (Entry 3*i + j is del f_j/del x_i).
   * \note The jacobian will be
   *            (1)              (1 0)             (1 0 0)
   * dim 1: J = (0)   dim 2: J = (0 1)  dim 3: J = (0 1 0)
   *            (0)              (0 0)             (0 0 1)
   */
  virtual void        t8_geom_evalute_jacobian (t8_cmesh_t cmesh,
                                                t8_gloidx_t gtreeid,
                                                const double *ref_coords,
                                                double *jacobian) const;


  /** Update a possible internal data buffer for per tree data.
   * This function is called before the first coordinates in a new tree are
   * evaluated. You can use it for example to load the vertex coordinates of the 
   * tree into an internal buffer (as is done in the linear geometry).
   * \param [in]  cmesh      The cmesh.
   * \param [in]  gtreeid    The glocal tree.
   */
  virtual void        t8_geom_load_tree_data (t8_cmesh_t cmesh,
                                              t8_gloidx_t gtreeid);

  inline const void  *t8_geom_get_bspline ()
  {
    return bspline;
  }

private:
  t8_geom_load_tree_data_fn load_tree_data; /**< The function to load the tree data. */

  const void         *tree_data;        /** Tree data pointer that can be set in \a load_tree_data and 
                                           is passed onto \a analytical_function and \a jacobian. */

  const Handle_Geom_BSplineSurface         bspline;        /** Additional user data pointer that can be set in constructor
                                         * and modified via \ref t8_geom_analytic_get_user_data. */
};

/* TODO: Document */
void                t8_geom_load_tree_data_vertices (t8_cmesh_t cmesh,
                                                     t8_gloidx_t gtreeid,
                                                     const void
                                                     **vertices_out);


#endif /* !T8_GEOMETRY_BSPLINE_HXX! */
