// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;



/**
 * Interface for all classes that create skolem symbols for various
 * kinds of schema variables
 */
public interface SkolemBuilder {

    /**
     * Return an iterator with all results (it can be necessary to
     * instantiate schema variables in multiple ways to cover all
     * possible usages)
     */
    IteratorOfSkolemSet build ();

}
