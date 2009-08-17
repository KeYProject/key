// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.incclosure;

import java.util.Iterator;


public interface Merger {

    /**
     * Reparent this merger; an implementing class should make
     * appropriate "reset"-calls to the new parent
     */
    void           setParent     ( Sink p_parent );

    /**
     * Inputs offered by this merger
     */
    Iterator<Sink> getSinks      ();

    /**
     * @return true iff the whole subtree of sinks below this merger
     * has seen consistent constraints
     */
    boolean        isSatisfiable ();

}
