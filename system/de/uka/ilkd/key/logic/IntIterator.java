// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.logic;


/** implemented by iterators of primitive type int */
public interface IntIterator {

    /** @return Integer the next element of collection */
    int next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

