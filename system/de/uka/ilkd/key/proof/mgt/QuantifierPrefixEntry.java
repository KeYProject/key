// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;


/**
 * Immutable class for representing information about the quantification of a
 * formula. The quantifier in <code>all x:int. phi</code> is represented by an
 * object <code>new QuantifierPrefixEntry(x, true)</code>
 */
public class QuantifierPrefixEntry {
    private final boolean universal;
    private final QuantifiableVariable variable;
    
    public QuantifierPrefixEntry (final QuantifiableVariable variable,
                                  final boolean universal) {
        this.variable = variable;
        this.universal = universal;
    }
        
    public boolean isUniversal () {
        return universal;
    }
    
    public QuantifiableVariable getVariable () {
        return variable;
    }

    /**
     * @return an entry in which universal and existential quantifiers are
     *         switched
     */
    public QuantifierPrefixEntry invert() {
        return new QuantifierPrefixEntry ( getVariable (), !isUniversal () );
    }
    
    public static ListOfQuantifierPrefixEntry invert (ListOfQuantifierPrefixEntry list) {
        if ( list.isEmpty () ) return list;

        return invert ( list.tail () ).prepend ( list.head ().invert () );
    }
    
    /**
     * @return an entry object that represents the top-level quantifier of the
     *         given formula
     *
     * @pre t.sort() == Sort.FORMULA && t.op() instanceof Quantifier
     */
    public static QuantifierPrefixEntry createFor (Term t) {
        Debug.assertTrue ( t.sort () == Sort.FORMULA
                           && t.op () instanceof Quantifier );
        
        return new QuantifierPrefixEntry ( t.varsBoundHere ( 0 )
                                           .getQuantifiableVariable ( 0 ),
                                           t.op () == Op.ALL );
    }
    
    /**
     * Represent the quantifier prefix of a formula as a list of prefix entries 
     *
     * @pre t.sort() == Sort.FORMULA
     */
    public static ListOfQuantifierPrefixEntry extractPrefix (Term t) {
        Debug.assertTrue ( t.sort () == Sort.FORMULA );

        ListOfQuantifierPrefixEntry res = SLListOfQuantifierPrefixEntry.EMPTY_LIST;
        while ( t.op () instanceof Quantifier ) {
            res = res.append ( QuantifierPrefixEntry.createFor ( t ) );
            t = t.sub ( 0 );
        }

        return res;
    }
    
    /**
     * Convert a sequence of <code>QuantifiableVariable</code>s to a prefix list
     */
    public static ListOfQuantifierPrefixEntry toUniversalList (Iterator it) {
        ListOfQuantifierPrefixEntry res = SLListOfQuantifierPrefixEntry.EMPTY_LIST;
        while ( it.hasNext () ) {
            final QuantifiableVariable var = (QuantifiableVariable)it.next ();
            res = res.append ( new QuantifierPrefixEntry ( var, true ) );
        }
        return res;
    }
}
