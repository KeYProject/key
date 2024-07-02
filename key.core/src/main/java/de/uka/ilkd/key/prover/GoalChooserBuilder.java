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

package de.uka.ilkd.key.prover;

/**
 * interface to be implemented by builders returning a 
 * goal chooser
 */
public interface GoalChooserBuilder {

    /** returns a new goal chooser */
    GoalChooser create();

    /** returns a clone of this goal chooser */
    GoalChooserBuilder copy();
    
    /** returns the name of the goal chooser */
    String name();
}