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

package de.uka.ilkd.key.rule.inst;
import de.uka.ilkd.key.java.ProgramElement;

/** This class is used to store the instantiation of a schemavarible
 * if it is a ProgramElement.
 */
public class ProgramInstantiation extends InstantiationEntry<ProgramElement> {
   
    /** creates a new ContextInstantiationEntry 
     * @param pe the ProgramElement the SchemaVariable is instantiated with
     */
    ProgramInstantiation(ProgramElement pe) {
	super(pe);
    }
}