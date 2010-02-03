// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;


/** Class representing the intersection of a set of constraints
 * (i.e. of arbitrary objects implementing the
 * "Constraint"-interface). Intersection means the constraint allowing
 * an instantiation of metavariables iff there exists a constraint
 * within the set allowing this instantiation.
 */

public class IntersectionConstraint implements Constraint {

    /**
     * Elements of the set this constraint is the intersection of;
     * objects having "subConstraints" with less than two elements are
     * not well-formed, and the list must not contain two different
     * elements from which one is stronger than the other.
     */
    private ListOfConstraint subConstraints = SLListOfConstraint.EMPTY_LIST;

    /**
     * Use the static attributes of "Constraint" for new constraints
     */
    protected IntersectionConstraint () {}

    /** returns true if Bottom
     * @return true if Bottom 
     */
    public boolean isBottom() {
	// There is only one bottom element which is an
	// EqualityConstraint
	return false;
    }

    /** a constraint being instance of this class is satisfiable. If a
     * method realizes that an unsatisfiable Constraint would be built
     * because of failed unification, cycle or s.th. similar it
     * returns the singleton TOP being instance of the subclass Top
     * @return true always 
     */
    public boolean isSatisfiable() {
	return true;
    }

    /**
     * Currently not needed, should return something more specific
     */
    public Term getInstantiation ( Metavariable p_mv ) {
	return TermFactory.DEFAULT.createFunctionTerm ( p_mv );
    }

    /**
     * Intersects p_c0 with p_c1, returning a constraint weaker or as
     * strong as both p_c0 and p_c1.
     * @param p_diff a constraint which is as strong (-> simple) as possible
     * satisfying
     * intersect ( p_c0, p_diff.val () ) == intersect ( p_c0, p_c1 )
     */
    public static Constraint intersect ( Constraint          p_c0,
					 Constraint          p_c1,
					 ConstraintContainer p_diff ) {
	if ( p_c0 instanceof IntersectionConstraint )
	    return ((IntersectionConstraint)p_c0).intersectHelp ( p_c1, p_diff );
	
	IntersectionConstraint res = new IntersectionConstraint ();
	res.subConstraints         = res.subConstraints.prepend ( p_c0 );
	return res.intersectHelp ( p_c1, p_diff );
    }

    public static Constraint intersect ( Constraint          p_c0,
					 Constraint          p_c1 ) {
	ConstraintContainer cc = new ConstraintContainer ();
	return intersect ( p_c0, p_c1, cc );
    }


    /**
     * Intersects this constraint with p_co.
     * @param p_diff a constraint which is as strong as possible
     * satisfying 
     * this.intersectHelp ( p_diff.val () ) == this.intersectHelp ( p_co )
     * @return A constraint representing the intersection of this and
     * p_co
     */
    protected Constraint intersectHelp ( Constraint          p_co,
					 ConstraintContainer p_diff ) {

	IntersectionConstraint res  = new IntersectionConstraint ();
	BooleanContainer       bc   = new BooleanContainer       ();
	IteratorOfConstraint   it;
	IntersectionConstraint diff = new IntersectionConstraint ();
	Constraint             c;

	res.subConstraints = subConstraints;

	if ( p_co instanceof IntersectionConstraint )
	    it = ((IntersectionConstraint)p_co).subConstraints.iterator ();
	else
	    it = SLListOfConstraint.EMPTY_LIST.prepend ( p_co ).iterator ();

	while ( it.hasNext () ) {
	    c      = it.next ();
	    res    = res.intersectHelp2 ( c, bc );
	    if ( !bc.val () )
		diff.subConstraints = diff.subConstraints.prepend ( c );
	}

	p_diff.setVal ( diff.intersectSimplify () );

	if ( diff.subConstraints == SLListOfConstraint.EMPTY_LIST )
	    return intersectSimplify ();

	res.subConstraints = res.subConstraints.prepend ( diff.subConstraints );
	return res.intersectSimplify ();

    }


    /**
     * Removes all elements from "this.subConstraints" that are
     * stronger than "p_co". Iff "p_co" is stronger than any element
     * of "this.subConstraints", "p_stronger" is set to true (and
     * "this" is returned). The return value may in fact be a not
     * well-formed object of this class ("subConstraints" may be empty
     * or contain only one element), that can be made correct by
     * calling "intersectSimplify".
     */
    protected IntersectionConstraint intersectHelp2 ( Constraint       p_co,
						      BooleanContainer p_stronger ) {

	IntersectionConstraint res;
	IteratorOfConstraint   it;
	Constraint             c;

	res = new IntersectionConstraint ();
	it  = subConstraints.iterator ();

	while ( it.hasNext () ) {
	    c = it.next ();

	    // Constraint to add is stronger than an existing
	    // element (-> can be ignored)
	    if ( p_co.isAsStrongAs ( c ) ) {
		p_stronger.setVal ( true );
		return this;
	    }

	    // Constraint to add is weaker than an existing
	    // element (-> this element can be removed)
	    if ( !p_co.isAsWeakAs ( c ) ) // otherwise keep the element
		res.subConstraints = res.subConstraints.prepend ( c );
	}

	p_stronger.setVal ( false );

	return res;
	
    }


    /**
     * Make an "IntersectionConstraint" well-formed
     */
    protected Constraint intersectSimplify () {
	if ( subConstraints == SLListOfConstraint.EMPTY_LIST )
	    return Constraint.TOP;

	if ( subConstraints.tail () == SLListOfConstraint.EMPTY_LIST )
	    return subConstraints.head ();

	return this;
    }


    /** executes unification for terms t1 and t2
     * @param t1 Term to be unified 
     * @param t2 term to be unified
     * @param services a Namespace where new sorts that may be created when 
     * unifying are added. If the value is null unifying will fail if new sorts 
     * are required for a succesfull unification
     * @return TOP if not possible, else a new constraint with after
     * unification of t1 and t2
     */
    public Constraint unify(Term t1, Term t2, Services services) {
	return join ( Constraint.BOTTOM.unify ( t1, t2, services ), services );
    }

        
    /** executes unification for terms t1 and t2. 
     * @param t1 Term to be unfied 
     * @param t2 Term to be unfied
     * @param services a Namespace where new sorts that may be created when 
     * unifying are added. If the value is null unifying will fail if new sorts 
     * are required for a succesfull unification
     * @param unchanged  true iff the new constraint is subsumed by
     * this one
     * @return TOP if not possible, else a new constraint with after
     * unification of t1 and t2
     */
    // TODO
    public Constraint unify(Term t1, Term t2, Services services, 
            BooleanContainer unchanged) {
	unchanged.setVal ( false );
	return unify ( t1, t2, services );
    }


    /** joins the given constraint with this constraint and returns
     * the joint new constraint.  Every implementing class should
     * handle the cases co == TOP and ( co instanceof EqualityConstraint ).
     * @param co Constraint to be joined with this one
     * @para, sort_ns a Namespace where new sorts that may be created when 
     * unifying are added. If the value is null unifying and therewith joining 
     * will fail if new sorts are required
     * @return the joined constraint 
     */	
    public Constraint join(Constraint co, Services services) {
	IteratorOfConstraint it  = subConstraints.iterator ();
	Constraint           res = Constraint.TOP;

	while ( it.hasNext () )
	    res = IntersectionConstraint.intersect ( res, co.join ( it.next (), services ) );

	return res;
    }
    

    /** joins constraint co with this constraint and returns the joint
     * new constraint. The BooleanContainer is used to wrap a second
     * return value and indicates a subsumption of co by this
     * constraint. Every implementing class should handle the cases co
     * == TOP and ( co instanceof EqualityConstraint ).
     * @param co Constraint to be joined with this one
     * @param services a Namespace where new sorts that may be created when 
     * unifying are added. If the value is null unifying will fail if new sorts 
     * are required for a succesfull unification
     * @param unchanged the BooleanContainers value set true, if this
     * constraint is stronger than co (false may stand for "don't
     * know")    
     * @return the joined constraint     
     */
    // TODO
    public Constraint join(Constraint co, Services services, BooleanContainer unchanged) {
	unchanged.setVal ( false );
	return join ( co, services );
    }


    /**
     * @return a constraint derived from this one by removing all
     * constraints on the given variable, which may therefore have any
     * value according to the new constraint (the possible values of
     * other variables are not modified)
     */
    public Constraint removeVariables ( SetOfMetavariable mvs ) {
	if ( mvs.iterator ().hasNext () ) {
	    Constraint           res = Constraint.TOP;
	    IteratorOfConstraint it  = subConstraints.iterator ();
	
	    while ( it.hasNext () )
		res = intersect ( res, it.next ().removeVariables ( mvs ) );

	    return res;
	}

	return this;
    }


    /** @return String representation of the constraint */
    public String toString() {
	return subConstraints.toString ();
    }

    /** checks equality of constraints by subsuming relation
     */
    public boolean equals ( Object obj ) {
	if ( obj instanceof Constraint ) {
	    Constraint c = (Constraint)obj;
	    return isAsStrongAs ( c ) && isAsWeakAs ( c );
	}
	return false;
    }

    /**
     * @return true iff this constraint is as strong as "co",
     * i.e. every instantiation satisfying "this" also satisfies "co".
     */
    public boolean isAsStrongAs ( Constraint co ) {
	IteratorOfConstraint it = subConstraints.iterator ();
	while ( it.hasNext () ) {
	    if ( !it.next ().isAsStrongAs ( co ) )
		return false;
	}
	return true;
    }

    /**
     * @return true iff this constraint is as weak as "co",
     * i.e. every instantiation satisfying "co" also satisfies "this".
     */
    public boolean isAsWeakAs ( Constraint co ) {
	if ( co instanceof IntersectionConstraint ) {
	    IteratorOfConstraint it = 
		((IntersectionConstraint)co).subConstraints.iterator ();
	    while ( it.hasNext () ) {
		if ( !isAsWeakAs ( it.next () ) )
		    return false;
	    }
	    return true;
	} else
	    return isAsWeakAsInteger ( co );
    }

    /**
     * Same as "isAsWeakAs" for "co" not an IntersectionConstraint
     */
    protected boolean isAsWeakAsInteger ( Constraint co ) {
	// Under some assumptions this can be reduced to: one element
	// of this intersection is weaker than "co"
	IteratorOfConstraint it = subConstraints.iterator ();
	while ( it.hasNext () ) {
	    if ( it.next ().isAsWeakAs ( co ) )
		return true;
	}
	return false;
    }
        
    public int hashCode () {
        //%% HACK
        return 0;
    }
}
