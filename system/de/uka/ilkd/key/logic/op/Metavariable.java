// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public class Metavariable extends TermSymbol
    implements ParsableVariable, Comparable {

    // Used to define an alternative order of all existing
    // metavariables
    private static int maxSerial = 0;
    private        int serial;
    
    private final boolean isTemporaryVariable;
    
    private synchronized void setSerial () {
	serial = maxSerial++;
    }

    private Metavariable(Name name, Sort sort, boolean isTemporaryVariable) {
	super(name, sort);
	if ( sort == Sort.FORMULA ) {
	    throw new RuntimeException(
		 "Attempt to create metavariable of type formula");
	}
	this.isTemporaryVariable = isTemporaryVariable;
	setSerial ();
    }

    public Metavariable (Name name, Sort sort) {
        this ( name, sort, false );
    }

    public static Metavariable createTemporaryVariable (Name name, Sort sort) {
        return new Metavariable ( name, sort, true );
    }
    

    /** @return true iff number of subterms of term is 0
     */
    public boolean validTopLevel(Term term){
        return term.arity()==0;
    }

    public String toString() {
	return name()+":"+sort();
    }

   /** @return arity of the Metavariable as int */
    public int arity() {
	return 0;
    }

    public int compareTo ( Object p ) {
	if ( p == this )
	    return 0;
	if ( p == null )
	    throw new NullPointerException ();

	// throws a ClassCastException on error
	final Metavariable cmp = (Metavariable)p;

	// temporary variables are the greatest ones
	if ( isTemporaryVariable () ) {
            if ( !cmp.isTemporaryVariable () ) return 1;
        } else {
            if ( cmp.isTemporaryVariable () ) return -1;
        }
    
	int t = name ().toString ().compareTo ( cmp.name ().toString () );
	if ( t == 0 )
	    return serial < (cmp).serial ? -1 : 1;
	return t;
    }
    
    /**
     * @return Returns the isTemporaryVariable.
     */
    public boolean isTemporaryVariable () {
        return isTemporaryVariable;
    }
}
