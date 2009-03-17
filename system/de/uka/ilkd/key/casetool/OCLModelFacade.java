// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.casetool;

// attention: do not import java.util.Collection
// The tudresden-package contains a class with the same name
import tudresden.ocl.check.types.Any;

/**
 * @deprecated
 */
public class OCLModelFacade extends OCLParserModelFacade {

    private HashMapOfClassifier classifiers;

    public OCLModelFacade(HashMapOfClassifier classifiers) {
	this.classifiers = classifiers;
	
    }

    public Any getClassifier(String name) {
	return classifiers.getClassifier(name);
    }

    public String toString() {
	return classifiers.toString();
    }

}
