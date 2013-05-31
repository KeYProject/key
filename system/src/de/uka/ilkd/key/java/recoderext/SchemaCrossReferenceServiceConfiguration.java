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


// This file is part of the RECODER library and protected by the LGPL.
package de.uka.ilkd.key.java.recoderext;

import recoder.ProgramFactory;
import recoder.service.SourceInfo;
import de.uka.ilkd.key.util.KeYExceptionHandler;

public class SchemaCrossReferenceServiceConfiguration
    extends KeYCrossReferenceServiceConfiguration {
  
    public SchemaCrossReferenceServiceConfiguration(KeYExceptionHandler keh) {
	super(keh);
    }

    /** we need another factory for some new program elements */
    protected ProgramFactory makeProgramFactory() {
	return SchemaJavaProgramFactory.getInstance();
    }

    /**
       The cross reference source info is a subclass of the source info,
       so this class simply overrides the source info factory method.
     */
    protected SourceInfo makeSourceInfo() {
 	return new SchemaCrossReferenceSourceInfo(this);
    }  
 

}

