// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;

/**
 * generates the proof obligation establishing that a given state describes a
 * legal pointer structure, i.e. that serveral system invariants are satisfied,
 * like no created object references a non-created one.
 */
public class InReachableStatePOBuilder extends AbstractInReachableStatePOBuilder {

    public InReachableStatePOBuilder(Services services) {
	super(services);
    }

}
