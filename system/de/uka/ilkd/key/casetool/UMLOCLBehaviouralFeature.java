// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.casetool;

import tudresden.ocl.check.types.Type;

/**
 * @deprecated
 */
public class UMLOCLBehaviouralFeature extends UMLOCLFeature {

    String name;
    Type[] params;
    Type ret;

    public UMLOCLBehaviouralFeature(String n, Type r) {
	name=n;
	ret=r;
	params=new Type[0];
    }

    public UMLOCLBehaviouralFeature(String n, Type r, Type p) {
	name=n;
	ret=r;
	params=new Type[1];
	params[0]=p;
    }

    public UMLOCLBehaviouralFeature(String n, Type r, Type[] ps) {
	name=n;
	ret=r;
	params=ps;
    }

    public UMLOCLBehaviouralFeature(String n, Type[] ps) {
	name=n;
	params=ps;
    }

    public String getName() {
	return name;
    }

    public Type getType() {
	return ret;
    }

    public boolean isQuery() {
	return true;
    }

    public Type[] getParameters() {
	return params;
    }
}
