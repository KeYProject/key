// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.translation.SLResolverManager;
import de.uka.ilkd.key.speclang.translation.SLCollection;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationExceptionManager;
import de.uka.ilkd.key.util.Debug;


class JMLResolverManager extends SLResolverManager {

    public JMLResolverManager(JavaInfo javaInfo,
                              KeYJavaType specInClass,
                              SLTranslationExceptionManager eManager) {
        super(javaInfo, specInClass, eManager, true, true, true);
    }

    public SLExpression createSLExpression(Term t) {
        return new JMLExpression(t);
    }

    public SLExpression createSLExpression(KeYJavaType t) {
        return new JMLExpression(t);
    }

    // There is no collection type in JML
    public SLExpression createSLExpression(SLCollection t) {
        Debug.fail();
        return null;
    }

}
