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

package de.uka.ilkd.key.java;


/**
 *  References are uses of names, variables or members.
 *  They can have a name (such as TypeReferences) or be
 *  anonymous (such as ArrayReference).
 * taken from COMPOST and changed to achieve an immutable structure
 */

public interface Reference extends ProgramElement {
}