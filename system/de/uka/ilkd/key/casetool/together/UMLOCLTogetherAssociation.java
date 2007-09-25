// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.casetool.together;

import de.uka.ilkd.key.casetool.Multiplicity;
import de.uka.ilkd.key.casetool.UMLOCLAssociation;
import de.uka.ilkd.key.casetool.UMLOCLClassifier;


/**
 * @deprecated Replaced by Association.
 */
public class UMLOCLTogetherAssociation implements UMLOCLAssociation {

    private static final boolean DEBUG = false;

    private UMLOCLClassifier source, target;
    private String sourceRole, targetRole;
    private Multiplicity sourceMult, targetMult;

    public UMLOCLTogetherAssociation(UMLOCLClassifier source,
				     String sourceRole,
				     Multiplicity sourceMult,
				     UMLOCLClassifier target,
				     String targetRole,
				     Multiplicity targetMult) {
	if (DEBUG)
	    System.out.println("creating an association from "+
			       source.getName()+" to "+target.getName());
	this.source = source;
	this.target = target;
	this.sourceRole = sourceRole; 
	this.targetRole = targetRole; 
	this.sourceMult = sourceMult;
	this.targetMult = targetMult;
    }

    public UMLOCLClassifier getSource() {
	return source;
    }

    public UMLOCLClassifier getTarget() {
	return target;
    }

    public Multiplicity getSourceMultiplicity() {
	return sourceMult;
    }

    public Multiplicity getTargetMultiplicity() {
	return targetMult;
    }

    public String getSourceRole() {
	return sourceRole;
    }

    public String getTargetRole() {
	return targetRole;
    }

}
