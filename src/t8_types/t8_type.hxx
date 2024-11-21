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

/**
 * \file This files gives a template for strong types in t8code.
 */

#ifndef T8_TYPE_HXX
#define T8_TYPE_HXX

#include <t8.h>

/**
 * \brief An implementation of strong type with additional competences.
 *
 * This class template allows the creation of a type that can be extended with
 * multiple competences. Each competence is a template class that takes the
 * main type as a template parameter.
 * 
 * This is heavily inspired by (and taken from) https://www.fluentcpp.com/2016/12/08/strong-types-for-strong-interfaces/
 *
 * \tparam T The type of the value to be stored.
 * \tparam Parameter An additional parameter for the type.
 * \tparam competence Variadic template parameter for the competences.
 */
template <typename T, typename Parameter, template <typename> class... competence>
class T8Type: public competence<T8Type<T, Parameter, competence...>>... {
 public:
  explicit T8Type (T const& value): value_ (value)
  {
  }

  /**
   * \brief Construct a new T8Type object
   * 
   * \tparam T_ref 
   * \param value 
   * 
   * \note This constructor is only enabled if T is not a reference.
   */
  template <typename T_ref = T>
  explicit T8Type (T&& value, typename std::enable_if<!std::is_reference<T_ref> {}, std::nullptr_t>::type = nullptr)
    : value_ (std::move (value))
  {
  }

  T&
  get ()
  {
    return value_;
  }

  T const&
  get () const
  {
    return value_;
  }

 private:
  T value_;
};

#endif /* T8_TYPE_HXX */
