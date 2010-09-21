// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.speclang.translation.*;


class JMLResolverManager extends SLResolverManager {

    public JMLResolverManager(JavaInfo javaInfo,
                              KeYJavaType specInClass,
                              ParsableVariable selfVar,
                              SLTranslationExceptionManager eManager) {
        super(eManager, specInClass, selfVar, false);
        addResolver(new JMLBuiltInPropertyResolver(javaInfo, this));
        addResolver(new SLAttributeResolver(javaInfo, this));        
        addResolver(new SLMethodResolver(javaInfo, this));
        addResolver(new SLTypeResolver(javaInfo, this));
    }
}
