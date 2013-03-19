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

import java.util.*;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.BooleanContainer;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;


/** 
 * This class implements a persistent constraint. The constraint
 * contains pairs of Metavariables X and Terms t meaning X=t. It
 * offers services like joining two Constraint objects, adding new
 * constraints to this one by unfying two terms and creating all
 * necessary Metavariable - Term pairs. There are no public
 * constructors to build up a new Constraint use the BOTTOM constraint
 * of the Constraint interface (static final class variable) and add
 * the needed constraints. If a constraint would not be satisfiable
 * (cycles, unification failed) the Constraint TOP of interface
 * Constraint is returned.
 */
@Deprecated
public class EqualityConstraint implements Constraint {
    
    /** contains a boolean value */ 
    private static final BooleanContainer
	CONSTRAINTBOOLEANCONTAINER=new BooleanContainer();

    /** stores constraint content as a mapping from Metavariable to
     * Term */
    private HashMap<Metavariable, Term> map;

    /** cache for return values of getInstantiation */
    private HashMap<Metavariable, Term> instantiationCache        = null;

    private Integer hashCode = null;
    
    /** Don't use this constructor, use Constraint.BOTTOM instead */
    public EqualityConstraint() {
	this ( new HashMap<Metavariable, Term> () );
    }

    private EqualityConstraint( HashMap<Metavariable, Term> map ) {
	this.map = map;
    }


    /* cache to speed up meta variable search */
    private static WeakHashMap<Term, ImmutableSet<Metavariable>> mvCache = 
	new WeakHashMap<Term, ImmutableSet<Metavariable>>(2000);
    
    
    public static ImmutableSet<Metavariable> metaVars(Term t) {
	
	if (mvCache.containsKey(t)) {
	    return mvCache.get(t);
	}
	
        ImmutableSet<Metavariable> metaVars = DefaultImmutableSet.<Metavariable>nil();
        
        Operator op = t.op();
        
        if(op instanceof Metavariable) {
            metaVars = metaVars.add((Metavariable) op);
        }
        for(int i = 0, ar = t.arity(); i < ar; i++) {
	    metaVars = metaVars.union(metaVars(t.sub(i)));
	}
        
        if (mvCache.size() > 10000) {
            mvCache.clear();
        }
        mvCache.put(t, metaVars);
        
        return metaVars;
    }
    
    protected synchronized Object clone () {
	EqualityConstraint res        =
	    new EqualityConstraint ( (HashMap<Metavariable, Term>)map.clone () );
	res.instantiationCache        =
	    instantiationCache == null ?
	    null :
	    (HashMap<Metavariable, Term>)instantiationCache.clone ();
	return res;
    }
    
    /** returns true if Bottom
     * @return true if Bottom 
     */
    final public boolean isBottom() {
	return map.isEmpty ();
    }

    /** a constraint being instance of this class is satisfiable. If a
     * method realizes that an unsatisfiable Constraint would be built
     * because of failed unification, cycle or s.th. similar it
     * returns the singleton TOP being instance of the subclass Top
     * @return true always 
     */
    final public boolean isSatisfiable() {
	return true;
    }


    /**
     * @return list of metavariables, instantiations of which may
     * restricted by this constraint
     */
    public Iterator<Metavariable> restrictedMetavariables () {
	return Collections.unmodifiableSet(map.keySet ()).iterator ();
    }

    /**      
     * @return The most general known term that is more defining than
     * p_mv itself by which p_mv can be replaced if the constraint is
     * valid (or null if the constraint allows arbitrary
     * instantiations of p_mv). This is just the entry of map.
     */
    public Term getDirectInstantiation ( Metavariable p_mv ) {
	return map.get ( p_mv );
    }


    /**
     * @return the term by which p_mv is instantiated by the most
     * general substitution satisfying the constraint
     */
    public synchronized Term getInstantiation (Metavariable p_mv) {
        Term t = null;
        if ( instantiationCache == null )
            instantiationCache = new HashMap<Metavariable, Term> ();
        else
            t = instantiationCache.get ( p_mv );

        if ( t == null ) {
            t = map.get ( p_mv );
            if ( t == null )
                t = TermBuilder.DF.var ( p_mv );
            else
                t = instantiate ( t );

            instantiationCache.put ( p_mv, t );
        }

        return t;
    }

    private synchronized Term getInstantiationIfExisting (Metavariable p_mv) {
        if ( instantiationCache == null )
            return null;
        return instantiationCache.get ( p_mv );
    }

    /**
     * instantiatiates term <code>p</code> according to the instantiations
     * of the metavariables described by this constraint. 
     * @param p the Term p to be instantiated
     * @return the instantiated term 
     */
    private Term instantiate ( Term p ) {
	SyntacticalReplaceVisitor srVisitor =
	    new SyntacticalReplaceVisitor(this, null);
	p.execPostOrder ( srVisitor );
	return srVisitor.getTerm ();
    }


    /** 
     * unifies terms t1 and t2
     * @param t1 Term to be unified 
     * @param t2 term to be unified
     * @param services the Services providing access to the type model
     * (e.g. necessary when introducing intersection sorts) 
     * @return TOP if not possible, else a new constraint with after
     * unification of t1 and t2
     */
    public Constraint unify ( Term t1, Term t2, Services services  ) {
	return unify(t1, t2, services, CONSTRAINTBOOLEANCONTAINER);
    }

        
    /** executes unification for terms t1 and t2. 
     * @param t1 Term to be unfied 
     * @param t2 Term to be unfied
     * @param services the Services providing access to the type model
     * (e.g. necessary when introducing intersection sorts) 
     * @param unchanged true iff the new constraint equals this one
     * @return TOP if not possible, else a new constraint unifying t1
     * and t2 ( == this iff this subsumes the unification )
     */
    public Constraint unify ( Term             t1,
			      Term             t2,
                              Services        services,
			      BooleanContainer unchanged ) {
	final Constraint newConstraint = unifyHelp ( t1, t2, false, services );

        if ( !newConstraint.isSatisfiable () ) {
            unchanged.setVal ( false );
            return Constraint.TOP;
        }

	if ( newConstraint == this ) {
	    unchanged.setVal ( true );
	    return this;
	}

	unchanged.setVal ( false );
	return newConstraint;
    }

    /**
     * compare two quantifiable variables if they are equal modulo renaming
     * @param ownVar first QuantifiableVariable to be compared
     * @param cmpVar second QuantifiableVariable to be compared
     * @param ownBoundVars variables bound above the current position
     * @param cmpBoundVars variables bound above the current position
     */
    private static boolean compareBoundVariables
	(QuantifiableVariable ownVar,
	 QuantifiableVariable cmpVar,
	 ImmutableList<QuantifiableVariable> ownBoundVars, 
	 ImmutableList<QuantifiableVariable> cmpBoundVars) {	
	
        final int ownNum = indexOf ( ownVar, ownBoundVars );
        final int cmpNum = indexOf ( cmpVar, cmpBoundVars );
        
	if ( ownNum == -1 && cmpNum == -1 )
	    // if both variables are not bound the variables have to be the
	    // same object        
	    return ownVar == cmpVar;

	// otherwise the variables have to be bound at the same point (and both
	// be bound)
	return ownNum == cmpNum;
    }

    
    /**
     * @return the index of the first occurrence of <code>var</code> in
     *         <code>list</code>, or <code>-1</code> if the variable is not
     *         an element of the list
     */
    private static int indexOf (QuantifiableVariable var,
                                ImmutableList<QuantifiableVariable> list) {
        int res = 0;
        while ( !list.isEmpty () ) {
            if ( list.head () == var ) return res;
            ++res;
            list = list.tail ();
        }
        return -1;
    }
    

    /**
     * Compares two terms modulo bound renaming and return a (possibly new)
     * constraint object that holds the instantiations necessary to make the two
     * terms equal.
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @param ownBoundVars variables bound above the current position
     * @param cmpBoundVars variables bound above the current position
     * @param modifyThis
     *            <code>this</code> is an object that has just been created
     *            during this unification process
     * @param services the Services providing access to the type model
     * (e.g. necessary when introducing intersection sorts). Value
     *  <code>null</code> is allowed, but unification fails 
     *  (i.e. @link Constraint#TOP is returned), if e.g. intersection sorts are required. 
     * @return a constraint under which t0, t1 are equal modulo bound renaming.
     *         <code>this</code> is returned iff the terms are equal modulo
     *         bound renaming under <code>this</code>, or
     *         <code>modifyThis==true</code> and the terms are unifiable. For
     *         <code>!modifyThis</code> a new object is created, and
     *         <code>this</code> is never modified.
     *         <code>Constraint.TOP</code> is always returned for ununifiable
     *         terms
     */
    private Constraint unifyHelp ( Term                       t0,
                                   Term                       t1,
                                   ImmutableList<QuantifiableVariable> ownBoundVars, 
                                   ImmutableList<QuantifiableVariable> cmpBoundVars,
                                   NameAbstractionTable       nat,
                                   boolean                    modifyThis, 
                                   Services services ) {

	if ( t0 == t1 && ownBoundVars.equals ( cmpBoundVars ) )
                return this;
            
        final Operator op0 = t0.op ();

        if ( op0 instanceof QuantifiableVariable )
                return handleQuantifiableVariable ( t0,
                                                    t1,
                                                    ownBoundVars,
                                                    cmpBoundVars );

        final Operator op1 = t1.op ();

        if ( op1 instanceof Metavariable ) {
            if ( op0 == op1 ) return this;
            
            if ( op0 instanceof Metavariable )
                return handleTwoMetavariables ( t0, t1, modifyThis, services );
            
            if ( t0.sort ().extendsTrans ( t1.sort () ) )
                return normalize ( (Metavariable)op1, t0, modifyThis, services );

            return Constraint.TOP;
        } else if ( op0 instanceof Metavariable ) {
            if ( t1.sort ().extendsTrans ( t0.sort () ) )
                return normalize ( (Metavariable)op0, t1, modifyThis, services );
            
            return Constraint.TOP;
        }

        if ( ! ( op0 instanceof ProgramVariable ) && op0 != op1 )
                return Constraint.TOP;
        

        if ( t0.sort () != t1.sort () || t0.arity () != t1.arity () )
                return Constraint.TOP;


        nat = handleJava ( t0, t1, nat );
        if (nat == FAILED) return Constraint.TOP;


        return descendRecursively ( t0,
                                    t1,
                                    ownBoundVars,
                                    cmpBoundVars,
                                    nat,
                                    modifyThis,
                                    services);
    }

    /**
     * Resolve an equation <tt>X=Y</tt> (concerning two metavariables) by
     * introducing a third variable <tt>Z</tt> whose sort is the intersection
     * of the sorts of <tt>X</tt>,<tt>Y</tt> and adding equations
     * <tt>X=Z</tt>,<tt>Y=Z</tt>. NB: This method must only be called if
     * none of the sorts of <code>t0</code>,<code>t1</code> is subsort of
     * the other one. Otherwise the resulting equation might get commuted,
     * <tt>Z</tt> might occur on the left side of the new equations and
     * horrible things will happen.
     * 
     * @param t0
     * @param t1
     * @param services
     * @return the constraint 
     */
    private Constraint introduceNewMV (Term t0,
                                       Term t1,
                                       boolean modifyThis,
                                       Services services) {
/*        if (services == null) return Constraint.TOP;
        
        final ImmutableSet<Sort> set = 
            DefaultImmutableSet.<Sort>nil().add(t0.sort()).add(t1.sort());*/
//        assert false : "metavariables disabled";
        return Constraint.TOP;
//        final Sort intersectionSort = 
//            IntersectionSort.getIntersectionSort(set, services);
//                      
//        if (intersectionSort == null) {
//            return Constraint.TOP;
//        }
//        
//        // I think these MV will never occur in saved proofs, or?
//        
//        final Metavariable newMV = 
//            new Metavariable(new Name("#MV"+(MV_COUNTER++)), intersectionSort);
//        final Term newMVTerm = TermFactory.DEFAULT.createFunctionTerm(newMV);
//        
//        final Constraint addFirst = normalize ( (Metavariable)t0.op (),
//                                                newMVTerm,
//                                                modifyThis,
//                                                services );
//        if ( !addFirst.isSatisfiable () ) return Constraint.TOP;
//        return ( (EqualityConstraint)addFirst )
//                                    .normalize ( (Metavariable)t1.op (),
//                                                 newMVTerm,
//                                                 modifyThis || addFirst != this,
//                                                 services );
    }
   

    /**
     * used to encode that <tt>handleJava</tt> results in an unsatisfiable constraint
     * (faster than using exceptions)
     */
    private static NameAbstractionTable FAILED = new NameAbstractionTable();
    
    private static NameAbstractionTable handleJava (Term t0,
                                                    Term t1,
                                                    NameAbstractionTable nat) {


        if ( !t0.javaBlock ().isEmpty()
                || !t1.javaBlock ().isEmpty() ) {
            nat = checkNat ( nat );
            if ( ! t0.javaBlock ().equalsModRenaming ( t1.javaBlock (), nat ) ) {
                return FAILED; 
            }
        }

        if ( ! ( t0.op () instanceof SchemaVariable )
                && t0.op () instanceof ProgramVariable ) {
            if ( ! ( t1.op () instanceof ProgramVariable ) ) {
                return FAILED; 
            }
            nat = checkNat ( nat );
            if ( ! ( (ProgramVariable)t0.op () )
                    .equalsModRenaming ( (ProgramVariable)t1.op (), nat ) ) {
                return FAILED;
            }
        }
        
        return nat;
    }

    private Constraint descendRecursively 
                      (Term t0,
                       Term t1,
                       ImmutableList<QuantifiableVariable> ownBoundVars,
                       ImmutableList<QuantifiableVariable> cmpBoundVars,
                       NameAbstractionTable nat,
                       boolean modifyThis,
                       Services services) {
        Constraint newConstraint = this;

        for ( int i = 0; i < t0.arity (); i++ ) {
            ImmutableList<QuantifiableVariable> subOwnBoundVars = ownBoundVars;
            ImmutableList<QuantifiableVariable> subCmpBoundVars = cmpBoundVars;            
            
            if ( t0.varsBoundHere ( i ).size () != t1.varsBoundHere ( i ).size () )
                return Constraint.TOP;
            for ( int j = 0; j < t0.varsBoundHere ( i ).size (); j++ ) {
                final QuantifiableVariable ownVar =
                    t0.varsBoundHere ( i ).get ( j );
                final QuantifiableVariable cmpVar =
                    t1.varsBoundHere ( i ).get ( j );
                if ( ownVar.sort () != cmpVar.sort () ) return Constraint.TOP;

                subOwnBoundVars = subOwnBoundVars.prepend ( ownVar );
                subCmpBoundVars = subCmpBoundVars.prepend ( cmpVar );
            }

            newConstraint = ( (EqualityConstraint)newConstraint )
                            .unifyHelp ( t0.sub ( i ), t1.sub ( i ),
                                         subOwnBoundVars, subCmpBoundVars,
                                         nat, modifyThis, services );
                                            
            if ( !newConstraint.isSatisfiable () ) return Constraint.TOP;
            modifyThis = modifyThis || newConstraint != this; 
        }

        return newConstraint;
    }

    private static NameAbstractionTable checkNat (NameAbstractionTable nat) {
        if ( nat == null ) return new NameAbstractionTable ();
        return nat;
    }

    private Constraint handleTwoMetavariables (Term t0,
                                               Term t1,
                                               boolean modifyThis,
                                               Services services) {
        final Metavariable mv0 = (Metavariable)t0.op ();
        final Metavariable mv1 = (Metavariable)t1.op ();
        final Sort mv0S = mv0.sort ();
        final Sort mv1S = mv1.sort ();
        if ( mv1S.extendsTrans ( mv0S ) ) {
            if ( mv0S == mv1S ) {
                // sorts are equal use Metavariable-order to choose the left MV
                if ( mv0.compareTo ( mv1 ) >= 0 )
                    return normalize ( mv0, t1, modifyThis, services );
                return normalize ( mv1, t0, modifyThis, services );                
            }
            return normalize ( mv0, t1, modifyThis, services );
        } else if ( mv0S.extendsTrans ( mv1S ) ) {
            return normalize ( mv1, t0, modifyThis, services );                
        }
        
        // The sorts are incompatible. This is resolved by creating a new
        // metavariable and by splitting the equation into two
        return introduceNewMV ( t0, t1, modifyThis, services );
    }

    private Constraint handleQuantifiableVariable 
                          (Term t0,
                           Term t1,
                           ImmutableList<QuantifiableVariable> ownBoundVars,
                           ImmutableList<QuantifiableVariable> cmpBoundVars) {
        if ( ! ( ( t1.op () instanceof QuantifiableVariable ) && 
                 compareBoundVariables ( (QuantifiableVariable)t0.op (),
                                         (QuantifiableVariable)t1.op (),
                                         ownBoundVars,
                                         cmpBoundVars ) ) )
            return Constraint.TOP;
        return this;
    }

    /**
     * Unify t1 and t2
     * @param modifyThis
     *            <code>this</code> is an object that has just been created
     *            during this unification process
     * @param services the Services providing access to the type model
     * 
     * @return a constraint under which t0, t1 are equal modulo bound renaming.
     *         <code>this</code> is returned iff the terms are equal modulo
     *         bound renaming under <code>this</code>, or
     *         <code>modifyThis==true</code> and the terms are unifiable. For
     *         <code>!modifyThis</code> a new object is created, and
     *         <code>this</code> is never modified.
     *         <code>Constraint.TOP</code> is always returned for ununifiable
     *         terms
     */
    private Constraint unifyHelp (Term t1, Term t2, boolean modifyThis, Services services) {
	return unifyHelp ( t1, t2,
			   ImmutableSLList.<QuantifiableVariable>nil(), 
			   ImmutableSLList.<QuantifiableVariable>nil(),
			   null,
			   modifyThis, services);
    }


    /** 
     * checks for cycles and adds additional constraints if necessary 
     *
     * PRECONDITION: the sorts of mv and t match; if t is also a
     * metavariable with same sort as mv, the order of mv and t is
     * correct (using Metavariable.compareTo)
     *
     * @param mv Metavariable asked to be mapped to the term t
     * @param t the Term the metavariable should be mapped to (if there
     * are no cycles )
     * @param services the Services providing access to the type model
     * @return the resulting Constraint ( == this iff this subsumes
     * the new constraint )
     */ 
    private Constraint normalize(Metavariable mv, Term t,
                                 boolean modifyThis, 
                                 Services services) {
	// MV cycles are impossible if the orders of MV pairs are
	// correct

	if ( !t.isRigid () ) return Constraint.TOP;	    

        // metavariable instantiations must not contain free variables
        if ( t.freeVars ().size () != 0
                || ( modifyThis ? hasCycle ( mv, t ) : hasCycleByInst ( mv, t ) ) ) // cycle
            return Constraint.TOP;
        else if ( map.containsKey ( mv ) )
                return unifyHelp ( valueOf ( mv ), t, modifyThis, services );
        
        final EqualityConstraint newConstraint = getMutableConstraint ( modifyThis );
        newConstraint.map.put ( mv, t );
        
        return newConstraint;
    }

    private EqualityConstraint getMutableConstraint (boolean modifyThis) {
        if ( modifyThis ) return this;
        return new EqualityConstraint ( (HashMap<Metavariable, Term>)map.clone () );
    }

    /**
     * checks equality of constraints by subsuming relation (only equal if no
     * new sorts need to be introduced for subsumption)
     */
    public boolean equals ( Object obj ) {
    	if ( this == obj )
    	    return true;
	if ( obj instanceof Constraint ) {
	    Constraint c = (Constraint)obj;
	    if ( c instanceof EqualityConstraint )
		return map.keySet ().equals
		    ( ((EqualityConstraint)c).map.keySet () ) &&
		    join ( c, null ) == this && 
                    c.join ( this, null ) == c;
	    return isAsStrongAs ( c ) && isAsWeakAs ( c );
	}
	return false;
    }

    /**
     * @return true iff this constraint is as strong as "co",
     * i.e. every instantiation satisfying "this" also satisfies "co".
     */
    public boolean isAsStrongAs ( Constraint co ) {
	if ( this == co )
	    return true;
	if ( co instanceof EqualityConstraint )
	    // use necessary condition for this relation: key set of
	    // this is superset of key set of co
	    return
		map.keySet ().containsAll
		( ((EqualityConstraint)co).map.keySet () ) &&
		join ( co, null ) == this;
	return co.isAsWeakAs ( this );
    }

    /**
     * @return true iff this constraint is as weak as "co",
     * i.e. every instantiation satisfying "co" also satisfies "this".
     */
    public boolean isAsWeakAs ( Constraint co ) {
	if ( this == co )
	    return true;
	if ( co instanceof EqualityConstraint )
	    // use necessary condition for this relation: key set of
	    // co is superset of key set of this
	    return
		((EqualityConstraint)co).map.keySet ().containsAll
		( map.keySet () ) &&
		co.join ( this, null ) == co;
	return co.isAsStrongAs ( this );	
    }

    /** joins the given constraint with this constraint
     * and returns the joint new constraint. 
     * @param co Constraint to be joined with this one
     * @return the joined constraint 
     */	
    public Constraint join(Constraint co, Services services) { 
	return join(co, services, CONSTRAINTBOOLEANCONTAINER); 
    }
    

    /** joins constraint co with this constraint
     * and returns the joint new constraint. The BooleanContainer is
     * used to wrap a second return value and indicates a subsumption
     * of co by this constraint. 
     * @param co Constraint to be joined with this one
     * @param services the Services providing access to the type model
     * @param unchanged the BooleanContainers value set true, if this
     * constraint is as strong as co
     * @return the joined constraint     
     */
    public synchronized Constraint join (Constraint co, 
            Services services, 
            BooleanContainer unchanged) {
        if ( co.isBottom () || co == this ) {
            unchanged.setVal ( true );
            return this;
        } else if ( isBottom () ) {
            unchanged.setVal ( false );
            return co;
        }

        if ( ! ( co instanceof EqualityConstraint ) ) {
            // BUG: Don't know how to set p_subsumed (at least not
            // efficiently)
            unchanged.setVal ( false );
            return co.join ( this, services );
        }

        final ECPair cacheKey;

        lookup: synchronized ( joinCacheMonitor ) {
	    ecPair0.set ( this, co );
            Constraint res = joinCache.get ( ecPair0 );

            if ( res == null ) {
                cacheKey = ecPair0.copy ();
                res = joinCacheOld.get ( cacheKey );
                if ( res == null ) break lookup;
                joinCache.put ( cacheKey, res );
            }

            unchanged.setVal ( this == res );
            return res;
        }

        final Constraint res = joinHelp ( (EqualityConstraint)co, services );

        unchanged.setVal ( res == this );

        synchronized ( joinCacheMonitor ) {
            if ( joinCache.size () > 1000 ) {
                joinCacheOld.clear ();
                final HashMap<ECPair, Constraint> t = joinCacheOld;
                joinCacheOld = joinCache;
                joinCache = t;
            }

            joinCache.put ( cacheKey, res );
            return res;
        }
    }

        
    private Constraint joinHelp (EqualityConstraint co, Services services) {
        Constraint newConstraint = this;
        boolean newCIsNew = false;
        for (Map.Entry<Metavariable, Term> entry : co.map.entrySet ()) {
            newConstraint = ( (EqualityConstraint)newConstraint )
                .normalize ( entry.getKey (), entry.getValue (),
                             newCIsNew, services );
            if ( !newConstraint.isSatisfiable () )
                return Constraint.TOP;
            newCIsNew = newCIsNew || newConstraint != this;
        }

        if ( newConstraint == this )
            return this;

        return newConstraint;
    }
    
    /**
     * @return a constraint derived from this one by removing all
     * constraints on the given variable, which may therefore have any
     * value according to the new constraint (the possible values of
     * other variables are not modified)
     */
    public Constraint removeVariables ( ImmutableSet<Metavariable> mvs ) {
	if ( !mvs.isEmpty() && !isBottom () ) {
	    EqualityConstraint removeConstraint = new EqualityConstraint ();
	    EqualityConstraint newConstraint    = new EqualityConstraint ();

	    // Find equalities with removed metavariable as left side
            for ( Map.Entry<Metavariable, Term>  entry : map.entrySet() ) {
		if ( mvs.contains ( entry.getKey () ) )
		    removeConstraint.map.put
			( entry.getKey (), entry.getValue () );
		else
		    newConstraint   .map.put
			( entry.getKey (), entry.getValue () );
	    }

	    // Find equalities with removed metavariable as right side
	    final Iterator<Map.Entry<Metavariable, Term>> it = 
	        newConstraint.map.entrySet ().iterator ();
	    
	    while ( it.hasNext () ) {
	        Map.Entry<Metavariable, Term> entry = it.next ();
		if ( (entry.getValue ()).op () instanceof Metavariable &&
		     ( (entry.getKey   ()).sort () ==
		       (        entry.getValue ()).sort () ) &&
		     ( mvs.contains
		       ( (Metavariable)(entry.getValue ()).op () ) ) &&
		     !( removeConstraint.map.containsKey
			( (entry.getValue ()).op () ) ) ) {
		    removeConstraint.map.put
			( (Metavariable)(entry.getValue ()).op (),
			  TermBuilder.DF.var
			  ( entry.getKey () ) );
		    it.remove ();
		}
	    }

	    if ( !removeConstraint.map.isEmpty () ) {
		// Substitute removed variables occurring within right
		// sides of the remaining equalities

		// Usually at this point removeConstraint is not a
		// well-formed constraint, as the order of MV may be
		// wrong. However, "SyntacticalReplaceVisitor" doesn't
		// care about that.
		if ( newConstraint.map.isEmpty () )
		    return Constraint.BOTTOM;

		final Set<Map.Entry<Metavariable, Term>> entrySet = 
		    newConstraint.map.entrySet ();
		
		newConstraint = new EqualityConstraint ();

		for (final Map.Entry<Metavariable, Term> entry : entrySet) {		    
		    newConstraint.map.put ( entry.getKey (),
		                            removeConstraint.instantiate
		                            ( entry.getValue () ) );
		}

		return newConstraint;
	    }
	}

	return this;
    }

    /** checks if there is a cycle if the metavariable mv and Term
     * term would be added to this constraint e.g. X=g(Y), Y=f(X) 
     * @param mv the Metavariable   
     * @param term The Term 
     * @return a boolean that is true iff. adding a mapping (mv,term)
     * would cause a cycle 
     */
    private boolean hasCycle ( Metavariable mv, Term term ) {
        ImmutableList<Metavariable> body          = ImmutableSLList.<Metavariable>nil();
        ImmutableList<Term>         fringe        = ImmutableSLList.<Term>nil();
        Term               checkForCycle = term;
        
        while ( true ) {
            for (Metavariable metavariable : metaVars(checkForCycle)) {
                final Metavariable termMV = metavariable;
                if (!body.contains(termMV)) {
                    final Term termMVterm = getInstantiationIfExisting(termMV);
                    if (termMVterm != null) {
                        if (metaVars(termMVterm).contains(mv))
                            return true;
                    } else {
                        if (map.containsKey(termMV))
                            fringe = fringe.prepend(map.get(termMV));
                    }

                    if (termMV == mv) return true;

                    body = body.prepend(termMV);
                }
            }

            if ( fringe.isEmpty() ) return false;

            checkForCycle = fringe.head ();
            fringe        = fringe.tail ();
        }        
    }

    private boolean hasCycleByInst (Metavariable mv, Term term) {

        for (Metavariable metavariable : metaVars(term)) {
            final Metavariable termMV = metavariable;
            if (termMV == mv) return true;
            final Term termMVterm = getInstantiationIfExisting(termMV);
            if (termMVterm != null) {
                if (metaVars(termMVterm).contains(mv)) return true;
            } else {
                if (map.containsKey(termMV)
                        && hasCycle(mv, getDirectInstantiation(termMV)))
                    return true;
            }
        }

        return false;
    }
        
    /**
     * ONLY FOR TESTS DONT USE THEM IN ANOTHER WAY
     * 
     * @return true if metavar is contained as key
     */
    boolean isDefined ( Metavariable mv ) {
	return map.containsKey ( mv );
    }
    
    /** ONLY FOR TESTS DONT USE THEM IN ANOTHER WAY 
     * @return mapping to mv */
    Term valueOf ( Metavariable mv ) {
	return map.get ( mv );
    }

    /** @return String representation of the constraint */
    public String toString () {
	return map.toString ();
    }

    
    private static final class ECPair {
        private Constraint first;
        private Constraint second;
        private int hash;

        public boolean equals (Object o) {
            if ( ! ( o instanceof ECPair ) ) return false;
            final ECPair e = (ECPair)o;
            return first == e.first && second == e.second;
        }
        
	public void set ( Constraint first, Constraint second ) {
            this.first = first;
            this.second = second;
	    this.hash = first.hashCode() + second.hashCode();
	}

        public int hashCode () {
            return hash;
        }
        
        public ECPair copy () {
            return new ECPair ( first, second, hash );
        }
        
        public ECPair (Constraint first, Constraint second) {
	    set ( first, second );
        }

        public ECPair (Constraint first, Constraint second, int hash) {
            this.first = first;
            this.second = second;
	    this.hash = hash;
        }
    }
    
    private static final Object joinCacheMonitor = new Object();
    
    private static HashMap<ECPair, Constraint> joinCache = 
        new HashMap<ECPair, Constraint> ();
    private static HashMap<ECPair, Constraint> joinCacheOld = 
        new HashMap<ECPair, Constraint> ();
    
    private static final ECPair  ecPair0   = new ECPair ( null, null, 0 );

    public int hashCode () {
        if ( hashCode == null ) {
            int h = 0;
            final Iterator<Metavariable> it = restrictedMetavariables ();
            while ( it.hasNext () ) {
                final Metavariable mv = it.next ();
                h += mv.hashCode ();
                h += getInstantiation ( mv ).hashCode ();
            }

            hashCode = Integer.valueOf ( h );
        }

        return hashCode.intValue ();
    }
}
