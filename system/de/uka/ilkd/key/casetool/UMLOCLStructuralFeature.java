// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
public class UMLOCLStructuralFeature extends UMLOCLFeature {

  String name;
  Type type;

  public UMLOCLStructuralFeature(String n, Type t) {
    name=n;
    type=t;
  }

  public String getName() {
    return name;
  }

  public Type getType() {
    return type;
  }
}

