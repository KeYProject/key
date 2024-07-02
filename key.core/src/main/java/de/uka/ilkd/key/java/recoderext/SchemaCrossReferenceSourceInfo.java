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

package de.uka.ilkd.key.java.recoderext;

import recoder.ServiceConfiguration;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.java.Reference;
import recoder.java.declaration.VariableSpecification;
import recoder.java.reference.TypeReference;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.service.KeYCrossReferenceSourceInfo;

public class SchemaCrossReferenceSourceInfo extends KeYCrossReferenceSourceInfo {
    
    protected final PrimitiveType recoderTypeSVType;

    public SchemaCrossReferenceSourceInfo(ServiceConfiguration config) {
	super(config);
	recoderTypeSVType 
	    = new PrimitiveType("TypeSV", this);
    }    

    public void initialize(ServiceConfiguration cfg) {
	super.initialize(cfg);
	cfg.getChangeHistory().removeChangeHistoryListener(this);
    }

    public Type getType(TypeReference tr) {
	if (tr instanceof TypeSVWrapper) {
	    return recoderTypeSVType;
	} else {
	    return super.getType(tr);
	}
    }

    public Type getType(VariableSpecification vs) {
	if (vs.getExpressionCount()>0 
	    && vs.getExpressionAt(0) instanceof ProgramVariableSVWrapper) {
	    return recoderTypeSVType;
	} else {
	    return super.getType(vs);
	}
    }

    /** does not resolve the urq, just returns the argument
     */
    public Reference resolveURQ(UncollatedReferenceQualifier urq){
	return urq;
    }


}