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

/** this exception is thrown if non-rigid instantiation has been given
 * for a schema variable only allowing rigid instantiations */
public class RigidnessException extends IllegalInstantiationException {

    /**
     * 
     */
    private static final long serialVersionUID = 1109354128591892703L;

    public RigidnessException(String description) {
	super(description);
    } 


}