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


package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.BooleanContainer;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;

/**
 * Abstract constraint interface for constraints offering unification of terms
 * and joins. There are no public constructors to build up a new Constraint use
 * the BOTTOM constraint (static final class variable) and add the needed
 * constraints if a constraint would not be satisfiable (cycles, unification
 * failed) the Constraint TOP is returned. TOP is as well as BOTTOM a static
 * final class variable (means usage of singleton pattern for Constraints BOTTOM
 * and TOP). Unsatisfiable constrains should only be representated by the TOP
 * element.
 */

@Deprecated
public interface Constraint {

    /** unsatisfiable Constraint */
    Constraint TOP = new Top();

    /** standard constraint class implementing the offered functionality */
    Constraint BOTTOM = new EqualityConstraint();

    /**
     * returns true if Bottom
     * 
     * @return true if Bottom
     */
    boolean isBottom();

    /**
     * a constraint being instance of this class is satisfiable. If a method
     * realizes that an unsatisfiable Constraint would be built because of
     * failed unification, cycle or s.th. similar it returns the singleton TOP
     * being instance of the subclass Top
     * 
     * @return true always
     */
    boolean isSatisfiable();

    /**
     * @param services TODO
    * @return Find a term the given metavariable can be instantiated with which
     *         is consistent with every instantiation that satisfies this
     *         constraint (that means, the term such an instantiation
     *         substitutes the metavariable with can always be unified with the
     *         returned term).
     */
    Term getInstantiation(Metavariable p_mv, TermServices services);

    /**
     * tries to unify the terms t1 and t2
     * 
     * @param t1
     *            Term to be unified
     * @param t2
     *            Term to be unified
     * @param services
     *            the Services providing access to the type model the parameter
     *            may be <code>null</code> but then the unification fails (i.e. @link
     *            Constraint#TOP is returned) when accessing the type model
     *            (e.g. for introducing intersection sorts) would be necessary).
     * 
     * @return TOP if not possible, else a new constraint with after unification
     *         of t1 and t2
     */
    Constraint unify(Term t1, Term t2, TermServices services);

    /**
     * tries to unify terms t1 and t2.
     * 
     * @param t1
     *            Term to be unfied
     * @param t2
     *            Term to be unfied
     * @param services
     *            the Services providing access to the type model
     * @param unchanged
     *            true iff the new constraint equals this one
     * @return TOP if not possible, else a new constraint with after unification
     *         of t1 and t2
     */
    Constraint unify(Term t1, Term t2, TermServices services,
	    BooleanContainer unchanged);

    /**
     * @return true iff this constraint is as strong as "co", i.e. every
     *         instantiation satisfying "this" also satisfies "co".
     */
    boolean isAsStrongAs(Constraint co);

    /**
     * @return true iff this constraint is as weak as "co", i.e. every
     *         instantiation satisfying "co" also satisfies "this".
     */
    boolean isAsWeakAs(Constraint co);

    /**
     * checks equality of constraints
     */
    boolean equals(Object obj);

    /**
     * joins the given constraint with this constraint and returns the joint new
     * constraint. Every implementing class should handle the cases co == TOP
     * and ( co instanceof EqualityConstraint ).
     * 
     * @param co
     *            Constraint to be joined with this one
     * @param services
     *            the Services providing access to the type model
     * @return the joined constraint
     */
    Constraint join(Constraint co, TermServices services);

    /**
     * joins constraint co with this constraint and returns the joint new
     * constraint. The BooleanContainer is used to wrap a second return value
     * and indicates a subsumption of co by this constraint. Every implementing
     * class should handle the cases co == TOP and ( co instanceof
     * EqualityConstraint ).
     * 
     * @param co
     *            Constraint to be joined with this one
     * @param services
     *            the Services providing access to the type model
     * @param unchanged
     *            the BooleanContainers value set true, if this constraint is as
     *            strong as co
     * @return the joined constraint
     */
    Constraint join(Constraint co, TermServices services, BooleanContainer unchanged);

    /** @return String representation of the constraint */
    String toString();

    /** Constraint class for representating the TOP (unsatisfiable) constraint. */
    @Deprecated
    class Top implements Constraint {

	/** creation of TOP */
	public Top() {
	}

	/**
	 * is an unsatisfiable Constraint satisfiable? NO.
	 * 
	 * @return always false
	 */
	public boolean isSatisfiable() {
	    return false;
	}

	public Term getInstantiation(Metavariable p_mv, TermServices services) {
	    // As there is in fact no instantiation satisfying this
	    // constraint, we could return everything
	    return services.getTermBuilder().var(p_mv);
	}

	/**
	 * adding new constraints to an unsatisfiable constraint results in an
	 * unsatisfiable constraint so this one is returned
	 * 
	 * @return always this
	 */
	public Constraint unify(Term t1, Term t2, TermServices services) {
	    return this;
	}

	public Constraint unify(Term t1, Term t2, TermServices services,
		BooleanContainer unchanged) {
	    unchanged.setVal(true);
	    return this;
	}

	public boolean equals(Object obj) {
	    return (obj instanceof Top);
	}

	public boolean isAsStrongAs(Constraint co) {
	    // Nothing is stronger than this ...
	    return true;
	}

	public boolean isAsWeakAs(Constraint co) {
	    // Nothing is stronger than this, except another Top
	    // instance
	    return (co instanceof Top);
	}

	/**
	 * joint of Top and co is Top
	 * 
	 * @return this
	 */
	public Constraint join(Constraint co, TermServices services) {
	    return this;
	}

	/**
	 * joint of Top and co is Top and Top subsumes every constraint
	 * 
	 * @return this
	 */
	public Constraint join(Constraint co, TermServices services,
		BooleanContainer c) {
	    c.setVal(true);
	    return this;
	}

	/**
	 * returns true if Bottom
	 * 
	 * @return true if Bottom
	 */
	public boolean isBottom() {
	    return false;
	}

	/**
	 * @return String representing the TOP constraint
	 */
	public String toString() {
	    return "TOP";
	}

	public int hashCode() {
	    return 12345;
	}
    }

}
