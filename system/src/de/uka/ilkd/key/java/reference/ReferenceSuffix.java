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

import de.uka.ilkd.key.java.ModelElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Reference;
import de.uka.ilkd.key.java.SourceElement;

/**
 *    Reference suffix. There are only few pure suffices, e.g.
 *    {@link SuperConstructorReference}.
 *    This interface does not extend {@link Reference}, as
 *    {@link recoder.java.expression.ParenthesizedExpression} is a qualifier
 *    but not a reference per se.
 */

public interface ReferenceSuffix extends ModelElement, 
    ProgramElement, SourceElement {

    /**
     *      @return the prefix in the access path, or null if there is none.
     */
//   ReferencePrefix getReferencePrefix();
}
