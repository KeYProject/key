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

package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.KeYRecoderMapping;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.logic.NamespaceSet;

public class ParserConfig {

    private Services services;
    private NamespaceSet nss;

    
    public ParserConfig(Services services, 
			NamespaceSet nss) {
	this.services = services;
	this.nss      = nss;
    }


    public Services services() {
	return services;
    }

    public NamespaceSet namespaces() {
	return nss;
    }

    public JavaInfo javaInfo() {
	return services.getJavaInfo();
    }

    public KeYRecoderMapping keyRecoderMapping() {
	return services.getJavaInfo().rec2key();
    }

    public TypeConverter typeConverter() {
	return services.getTypeConverter();
    }

    public KeYCrossReferenceServiceConfiguration serviceConfiguration() {
	return services.getJavaInfo().
	    getKeYProgModelInfo().getServConf();
    }

}
