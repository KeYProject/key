// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.collection;

/** This interface declares a tupel of two values.
 * The first one is of type <S> and named key, the second one
 * is of type <T> and named value
 */

public interface ImmutableMapEntry<S,T> extends java.io.Serializable {

    /** @return the first part of the tupel */
    S key();

    /** @return the second part of the tupel */
    T value();
}