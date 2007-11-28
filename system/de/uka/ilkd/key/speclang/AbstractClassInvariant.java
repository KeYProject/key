// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.TermBuilder;


public abstract class AbstractClassInvariant implements ClassInvariant {
    protected static final TermBuilder tb = TermBuilder.DF;
    private final ModelClass modelClass;
    
    
    public AbstractClassInvariant(ModelClass modelClass) {
	this.modelClass = modelClass;
    }
    
    
    public ModelClass getModelClass() {
	return modelClass;
    }

    
    public KeYJavaType getKJT(Services services) {
	return services.getJavaInfo().getTypeByClassName(
					modelClass.getFullClassName());
    }
}
