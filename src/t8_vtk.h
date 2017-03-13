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

/** file t8_vtk.h
 * This header file collects macros that are needed for
 * the forest and cmesh vtk routines.
 * \see t8_forest_vtk.h \see t8_cmesh_vtk.h
 */

#ifndef T8_VTK_H
#define T8_VTK_H

#include <t8.h>

/* typedef and macros */

/* TODO: TOPIDX is deprecated, remove it */
#define T8_VTK_TOPIDX "Int32"
#define T8_VTK_LOCIDX "Int32"
/* TODO: Paraview has troubles with Int64, so we switch to Int32 and be careful.
 *       Investigate this further. See also vtk makro VTK_USE_64BIT_IDS */
#define T8_VTK_GLOIDX "Int32"

/* TODO: these macros need to be set by configure */
#ifndef T8_VTK_DOUBLES
#define T8_VTK_FLOAT_NAME "Float32"
#define T8_VTK_FLOAT_TYPE float
#else
#define T8_VTK_FLOAT_NAME "Float64"
#define T8_VTK_FLOAT_TYPE double
#endif

#ifndef T8_VTK_BINARY
#define T8_VTK_ASCII 1
#define T8_VTK_FORMAT_STRING "ascii"
#else
#define T8_VTK_FORMAT_STRING "binary"
#endif

T8_EXTERN_C_BEGIN ();

/* function declarations */
/* Writes the pvtu header file that links to the processor local files.
 * It is used by the cmesh and forest vtk routines.
 * This function should only be called by one process.
 * Return 0 on success. */
/* TODO: document */
int                 t8_write_pvtu (const char *filename, int num_procs,
                                   int write_tree, int write_rank,
                                   int write_level, int write_id);

T8_EXTERN_C_END ();

#endif /* !T8_VTK_H */