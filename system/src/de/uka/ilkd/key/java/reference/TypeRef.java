// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.util.ExtList;

public class TypeRef extends TypeReferenceImp {

    private KeYJavaType kjt = null;

    /** creates a type reference for the given KeYJavaType with
     * dimension 0 and creates a suitable package reference prefix
     * from the KeYJavaType. If this is not desired use the
     * constructor TypeRef(ProgramElementName, int, ReferencePrefix,
     * KeYJavaType) and take null as last argument.
     */
    public TypeRef(KeYJavaType kjt) {
	this(kjt, 0);
    }

    /** creates a type reference for the given KeYJavaType and the
     * given dimension and creates a suitable package reference prefix
     * from the KeYJavaType. If this is not desired use the constructor
     * TypeRef(ProgramElementName, int, ReferencePrefix, KeYJavaType)
     * and take null as last argument.
     */
    public TypeRef(KeYJavaType kjt, int dim) {
	super(new ProgramElementName(kjt.getName()), 
	      dim, kjt.createPackagePrefix());
	this.kjt = kjt;
    }


    public TypeRef(ExtList children, KeYJavaType kjt, int dim) {
	super(children, dim);
	this.kjt = kjt;
    }

    public TypeRef(ProgramElementName name, 
		   int dimension, 
		   ReferencePrefix prefix,
		   KeYJavaType kjt) {
	super(name, dimension, prefix);
	this.kjt = kjt;
    }

    public KeYJavaType getKeYJavaType() {
	return kjt;
    }

}
