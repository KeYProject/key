// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Represents a numerical quantifier like <tt>\product</tt> or 
 * <tt>\sum</tt>. A numerical quantifier 
 */
public class NumericalQuantifier extends Op {

    NumericalQuantifier(Name name) {
        super(name);
    }

    public int arity() {
        return 2;
    }

    public Sort sort(Term[] term) {
        return term[1].sort ();
    }

    public boolean validTopLevel(Term term) {
        return term.arity () == arity () && term.sub(0).sort() == Sort.FORMULA;
    }

}
