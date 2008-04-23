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

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.translation.SLExpression;


class JMLExpression extends SLExpression {

    private final Term typeofTerm;

    public JMLExpression(Term term) {
        super(term);
        this.typeofTerm = null;
    }

    public JMLExpression(KeYJavaType type) {
        super(type);
        this.typeofTerm = null;
    }
    
    /**
     * A JMLExpression resulting from the JML construct "\typeof(t)"
     * It is treated as a type-expression, i.e. super.isType() will be
     * true, but internally stores the argument <code>t</code>, which will
     * be used by the parser for translating e.g.
     * "\typeof(var) = \type(Typename)"
     */
    public JMLExpression(KeYJavaType type, Term t) {
        super(type);
        this.typeofTerm = t;
    }

    public Term getTypeofTerm() {
        return this.typeofTerm;
    }
}
