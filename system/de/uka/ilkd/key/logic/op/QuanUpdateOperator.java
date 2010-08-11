// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import java.lang.ref.WeakReference;
import java.util.*;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.updatesimplifier.GuardSatisfiabilityFormulaBuilder;
import de.uka.ilkd.key.rule.updatesimplifier.GuardSimplifier;
import de.uka.ilkd.key.util.Debug;


/**
 * <p>
 * Operator for simultaneous, guarded and quantified updates. In concrete
 * syntax, such updates have the shape
 * <tt> [ for (Variables) ] [ if (Formula) ] lhs := value
 *       ( , [ for (Variables) ] [ if (Formula) ] lhs := value ) * </tt>.
 * </p>
 * <p>
 * The update operator is uniquely defined by the contained locations, their
 * order, and the information which of the assigments are guarded (a boolean
 * array). This has some odd consequences of the sub terms of an update term as
 * given above:
 * <ol>
 * <li>Let <code> loc_1,...,loc_i </code> be local or static variables then
 * only the corresponding values <code>val_1, ..., val_n</code> are subterms
 * the locations itself are part of the operator.</li>
 * <li>For <code>loc_i (=r_i.a_i),...,loc_n(=r_n.a_n)</code> that refer to an
 * instance attribute, only their reference prefix <code>r_i</code> is a
 * subterm while the attribute <code> a_i </code> is part of the update
 * operator. If <code>loc_i</code> is an array <code>a[l]</code> then the
 * sort of <code> a </code> is fixed and <code>a, i</code> are sub terms</li>
 * </ol>
 * There are methods that return the location access part (attribute, local or
 * static variable) and also the complete n-th location as term.
 * </p>
 */
public class QuanUpdateOperator implements IUpdateOperator {
    
    private final static TermFactory tf = TermFactory.DEFAULT;
    private final static TermBuilder tb = TermBuilder.DF;
    
    /**
     * The signature that uniquely identifies instances of the quantified update
     * operator. This consists of the list of locations that are updated and a
     * boolean array telling which of these elementary updates is also equipped
     * with a guard
     */
    private static class QuanUpdateSignature {
        /** the locations access operators used by the update op */
        public final ImmutableArray<Location> locations;
        /** which of the update entries are equipped with a guard? */
        public final boolean[] guards;
        
        public QuanUpdateSignature (final Location[] locations,
                                    final boolean[] guards) {
            this.locations = new ImmutableArray<Location> ( locations );
            this.guards = guards.clone ();
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#equals(java.lang.Object)
         */
        public boolean equals (Object o2) {
            if ( !( o2 instanceof QuanUpdateSignature ) ) return false;
            final QuanUpdateSignature sig2 = (QuanUpdateSignature)o2;
            return locations.equals ( sig2.locations )
                   && Arrays.equals ( guards, sig2.guards );
        }
        
        /* (non-Javadoc)
         * @see java.lang.Object#hashCode()
         */
        public int hashCode () {
            int res = locations.hashCode ();
            // the following should be replaced with java.util.Arrays.hashCode
            // (Java 1.5)
            for ( int i = 0; i != guards.length; ++i ) {
                if ( guards[i] ) ++res;
                res *= 3;
            }
            return res;
        }
    }
    
    /**
     * name of the operator
     */
    private final Name name;

    /** the arity of this operator */
    private final int arity;

    private final QuanUpdateSignature signature;
    
    /**
     * table to determine the position of the value to a given location
     */
    private final int[] valuePositionTable;

    /**
     * Map from <code>QuanUpdateSignature</code> to
     * <code>QuanUpdateOperator</code>
     */
    private static final WeakHashMap<QuanUpdateSignature, WeakReference<QuanUpdateOperator>> updates = 
        new WeakHashMap<QuanUpdateSignature, WeakReference<QuanUpdateOperator>>();

    /**
     * returns the update operator for the given location order
     */
    public static QuanUpdateOperator createUpdateOp(Term[] locs,
                                                    boolean[] guards) {
        Location[] locOps = new Location[locs.length];
        for (int i = locs.length - 1; i >= 0; i--) {
            locOps[i] = (Location) locs[i].op();
        }
        return createUpdateOp(locOps, guards);
    }

    /**
     * @param guards
     *            boolean array telling which of the elementary updates are
     *            guarded
     * @return the update operator for the given location order
     */
    public static QuanUpdateOperator createUpdateOp(Location[] locs,
                                                    boolean[] guards) {
        final QuanUpdateSignature sig = new QuanUpdateSignature ( locs, guards );
        WeakReference<QuanUpdateOperator> qUpOp = updates.get(sig);
        QuanUpdateOperator result = qUpOp!=null?qUpOp.get():null;
        if (result == null) {
            result = new QuanUpdateOperator(sig);
            updates.put(sig, new WeakReference<QuanUpdateOperator>(result));
        }
        return result;
    }

    /**
     * creates the update operator for the given signature
     * 
     * @param name the Name of the quanified update operator
     * @param signature the {@link QuanUpdateSignature} of the update 
     * operator to be created 
     */
    private QuanUpdateOperator(Name name, QuanUpdateSignature signature) {
        this.name = name;
        this.signature = signature;
        this.valuePositionTable = new int[signature.locations.size()];

        fillValuePositionTable();
        this.arity = signature.locations.size() == 0 ? 1
                : valuePositionTable[valuePositionTable.length - 1] + 2;
    }

    /**
     * the given locations are the one to be updated by this operator  
     * @param signature the {@link QuanUpdateSignature} of the quantified update
     */
    private QuanUpdateOperator(QuanUpdateSignature signature) {
        this(new Name("quanUpdate("+signature.locations+")"), signature); 
    }

    /**
     * Replace the locations of this operator without changing anything else.
     * This must not change the number of locations, i.e.
     * <code>newLocs.length==locationCount()</code>
     */
    public IUpdateOperator replaceLocations (Location[] newLocs) {
        Debug.assertTrue ( newLocs.length == locationCount () );
        return createUpdateOp ( newLocs, signature.guards );
    }
    
    /**
     * returns the array of location operators which are updated
     */
    public ImmutableArray<Location> locationsAsArray() {
        return signature.locations;
    }

    /**
     * returns the number of locations
     * 
     * @return the number of locations as int
     */
    public int locationCount() {
        return locationsAsArray().size();
    }

    /**
     * returns the operator of <tt>n</tt>-th location
     */
    public Location location(int n) {
        return locationsAsArray().get(n);
    }

    /**
     * returns the number of the subterm representing the value to which
     * the locPos-th location is updated
     */
    public int valuePos(int locPos) {
        return valuePositionTable[locPos];
    }
        

    /**
     * @return <code>true</code> iff the elementary update with index
     *         <code>locPos</code> is guarded
     */
    public boolean guardExists(int locPos) {
        return signature.guards[locPos];
    }
    
    /**
     * @return the number of the subterm representing the guard constraining the
     *         <tt>locPos</tt> -th update, provided that this guard exists
     *         (otherwise <code>-1</code>)
     */
    public int guardPos (int locPos) {
        if ( !guardExists ( locPos ) ) return -1;
        if ( locPos == 0 ) return 0;
        return valuePos ( locPos - 1 ) + 1;
    }

    /**
     * @return the index of the first subterm belonging to update entry
     *         <code>locPos</code>
     */
    public int entryBegin(int locPos) {        
        if ( locPos == 0 ) return 0;
        return valuePos ( locPos - 1 ) + 1;
    }
    
    /**
     * @return the index after the last subterm belonging to update entry
     *         <code>locPos</code>. The entry is described within
     *         <tt>[entryBegin(i), entryEnd(i))</tt>
     */
    public int entryEnd (int locPos) {
        return valuePos ( locPos ) + 1;
    }
    
    /**
     * @return the index of the first subterm belonging to the location of entry
     *         <code>locPos</code>
     */
    public int locationSubtermsBegin (int locPos) {
        if ( guardExists ( locPos ) ) return entryBegin ( locPos ) + 1;
        return entryBegin ( locPos );
    }
    
    /**
     * @return the index after the last subterm belonging to the location of
     *         update entry <code>locPos</code>. The location is described
     *         within
     *         <tt>[locationSubtermsBegin(i), locationSubtermsEnd(i))</tt>
     */
    public int locationSubtermsEnd (int locPos) {
        return entryEnd ( locPos ) - 1;
    }
    
    /**
     * @return the variables that are quantified for the elementary update
     *         <code>locPos</code>
     */
    public ImmutableArray<QuantifiableVariable> boundVars (Term t, int locPos) {
        return t.varsBoundHere ( valuePos ( locPos ) );
    }
    
    /**
     * returns an array with all location positions of <code>loc</code>
     * 
     * @param loc a n Operator accessing a location
     * @return all location positions of <code>loc</code>
     */
    public int[] getLocationPos(Operator loc) {
        int size = 0;
        final int[] tempResult = new int[locationCount()];
        for (int i = 0; i < tempResult.length; i++) {
            if (location(i) == loc) {
                tempResult[size] = i;
                size++;
            }
        }
        final int[] result = new int[size];
        System.arraycopy(tempResult, 0, result, 0, size);

        return result;
    }

    /**
     * computes the position table used to determine at which sub term position
     * the value used to update the i-th location can be found.
     */
    private void fillValuePositionTable() {
        int pos = 0;
        for (int i = 0; i < valuePositionTable.length; i++) {
            pos += location(i).arity();
            if ( guardExists ( i ) ) ++pos;
            valuePositionTable[i] = pos;
            pos++;
        }
    }

    /**
     * returns the n-th location of the update as term
     * 
     * @param t
     *            Term with this operator as top level operator
     * @param n
     *            an int specifying the position of the requested location
     * @return the n-th location of term t updated by this operator
     */
    public Term location(Term t, int n) {
        Debug.assertTrue(t.op() == this, "Illegal update location access.");

        final Term[] sub = new Term [location ( n ).arity ()];

        for (int i = locationSubtermsBegin(n), j = 0;
             i != locationSubtermsEnd(n);
             ++i, ++j)
            sub[j] = t.sub(i);
        
        
        final ImmutableArray<QuantifiableVariable>[] vars = new ImmutableArray[sub.length];
        Arrays.fill(vars, Term.EMPTY_VAR_LIST);
        
        return tf.createTerm ( location ( n ),
                               sub,
                               vars,
                               JavaBlock.EMPTY_JAVABLOCK);
    }

    /**
     * returns value the n-th location is updated with
     * 
     * @param t
     *            Term with this operator as top level operator
     * @param n
     *            an int specifying the position of the location
     * @return the value the n-th location is updated with
     */
    public Term value (Term t, int n) {
        Debug.assertTrue ( t.op () == this, "Illegal update value access." );
        return t.sub ( valuePos ( n ) );
    }

    /**
     * returns the guard of the n-th update entry; if this entry does not have a
     * guard, <tt>TRUE</tt> is returned
     * 
     * @param t
     *            Term with this operator as top level operator
     * @param n
     *            an int specifying the position of the location
     * @return the guard of the n-th update entry
     */
    public Term guard (Term t, int n) {
        if ( !guardExists ( n ) )
            return getValidGuard();
        return t.sub ( guardPos ( n ) );
    }
    
    /** @return name of the operator */
    public Name name() {
        return name;
    }

    /**
     * returns the arity of the operator
     */
    public int arity() {
        return arity;
    }

    /**
     * the position of the term the quantified update is applied to  
     * @return the sub term position of the target term 
     */      
    public int targetPos () {
        return arity () - 1;
    }

    /**
     * @return the index of the subterm representing the formula/term the update
     *         is applied to
     */
    public Term target (Term t) {
        return t.sub ( targetPos () );
    }

    /**
     * returns the sort a term would have if constructed with this operator and
     * the given sunterms. It is assumed that the term would be allowed if
     * constructed.
     * 
     * @param term
     *            an array of Term containing the subterms of a (potential)
     *            simultaneous update term
     * @return sort of the simultaneous update term consisting of the given
     *         subterms, if this op would be the top symbol
     */
    public Sort sort(Term[] term) {
        return term[targetPos()].sort();
    }

    /**
     * @return true if the value of "term" having this operator as top-level
     *         operator and may not be changed by modalities
     */
    public boolean isRigid(Term term) {
        return target(term).isRigid();
    }

    /**
     * checks whether the top level structure of the given {@link Term}is
     * syntactically valid, given the assumption that the top level operator of
     * the term is the same as this Operator. The assumption that the top level
     * operator and the operator are equal is NOT checked.
     * 
     * @return true iff the top level structure of the {@link Term}is valid.
     */
    public boolean validTopLevel(Term term) {
        if ( term.arity () != arity () ) return false;
        for ( int i = 0; i != locationCount (); ++i ) {
            if ( guardExists ( i )
                 && term.sub ( guardPos ( i ) ).sort () != Sort.FORMULA )
                return false;
        }
        return true;
    }

    /**
     * two concrete update operators match if their defining locations match,
     * and if the same elementary updates are guarded (that means that different
     * taclets/rules have to be written for guarded and unguarded updates, which
     * is not too bad because one hardly ever writes taclets that match on
     * updates anyway ;-)
     * 
     * @see de.uka.ilkd.key.logic.op.Operator#match
     *      (SVSubstitute,
     *      de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc, Services services) {
        MatchConditions result = mc;
        if (this == subst) return result;
        if (subst.getClass() != getClass()) {
            Debug.out("FAILED matching. Incomaptible operators " +
            "(template, operator)", this, subst);
            return null;
        }      
        final QuanUpdateOperator update = (QuanUpdateOperator)subst;
        if ( locationCount () == update.locationCount ()
             && Arrays.equals ( signature.guards, update.signature.guards ) ) {
            for (int i = 0, locs = locationCount(); i<locs; i++) {
                result = location(i).match(update.location(i), result, services);
                if (result == null) { // fail fast
                    Debug.out
                    ("FAILED. QuanUpdateOperator location mismatch " +
                            "(template, operator)", this, update);
                    return null;
                }
            }
            return result;
        }        
        Debug.out("FAILED matching. QuanUpdateOperator match failed because of" +
                " incompatible locations (template, operator)", this, subst);
        return null;
    }

    /**
     * returns a string representation of the update operator 
     */
    public String toString() {
        StringBuffer sb = new StringBuffer("quanUpdate(");
        for (int i = 0; i < locationCount(); i++) {
            sb.append(location(i));
            if (i < locationCount() - 1) {
                sb.append(" || ");
            }
        }
        sb.append("}");
        return sb.toString();
    }

    /**
     * The term class for quantified updates requires that the same variables
     * are quantified for all parts of an update entry (subterms of the
     * left-hand side, guard and the value); in principle this could also be
     * done more generally and with different variables. Given arrays of
     * variables for each entry part, an common array is constructed here
     * (unification). This can include bound renaming.
     * 
     * @param boundVarsPerSub
     *            the arrays of variables bound for each subterm
     * @param subs
     *            the subterms of the update entry. The components of this array
     *            are modified if bound renaming is necessary
     * @return the arrays of variables bound for each location
     */
    public ImmutableArray<QuantifiableVariable>[]
        toBoundVarsPerAssignment (ImmutableArray<QuantifiableVariable>[] boundVarsPerSub,
                                  Term[] subs) {
        final ImmutableArray<QuantifiableVariable>[] res = new ImmutableArray [locationCount()];

        for ( int i = 0; i != locationCount (); ++i )
            res[i] = BoundVariableTools.DEFAULT
                        .unifyBoundVariables ( boundVarsPerSub,
                                               subs,
                                               entryBegin ( i ),
                                               entryEnd ( i ) );

        return res;        
    }
    
    /**
     * The comparator that is used to sort the different assignments in an
     * update as totally as possible. This is done by first grouping different
     * kinds of top-level operators (local program variables, static attributes,
     * instance attributes and array accesses, other operators). Thereafter, we
     * sort according to the name of an operator. Because of last-win semantics,
     * updates that potentially clash (here simply: have the same top-level
     * operator) are not permuted.
     */
    private static class ElUpdateLocationComparator 
        implements Comparator<ElUpdateLocation> {
        private int primitiveLongCompare(long i, long j) {
            return (i < j ? -1 : (i == j ? 0 : 1));
        }

        public int compare(ElUpdateLocation elUpd1, ElUpdateLocation elUpd2) {
            // deliberately raise a ClassCastException for unsuitable o1, o2
            final Location pv1 = elUpd1.getLocation ();
            final Location pv2 = elUpd2.getLocation ();
            
            if ( elUpd1.locationNum == elUpd2.locationNum ) return 0;
            
            int cmpResult = getLocationKind ( pv1 ) - getLocationKind ( pv2 );
            if ( cmpResult != 0 ) return cmpResult;
            
            cmpResult = pv1.name ().compareTo ( pv2.name () );
            
            ////////////////////////////////////////////////////////////////////
            // beware, ugly HACK ahead:
            // because different array operators are different, but can still clash,
            // we must not reorder assignments to arrays
            if ( pv1 instanceof ArrayOp && pv2 instanceof ArrayOp ) cmpResult = 0;
            ////////////////////////////////////////////////////////////////////
            
            if ( cmpResult != 0 ) return cmpResult;
            
            final boolean bPV1 = pv1 instanceof ProgramVariable;
            final boolean bPV2 = pv2 instanceof ProgramVariable;
            cmpResult = bPV1 ?
                               (bPV2 ?
                                       primitiveLongCompare( ((ProgramVariable) pv1).id(),
                                                             ((ProgramVariable) pv2).id())
                                     : -1)
                             :
                               (bPV2 ? 1 : 0);
            if ( cmpResult != 0 ) return cmpResult;
            
            return elUpd1.locationNum - elUpd2.locationNum;
        }
        
        private int getLocationKind(Location location) {
            if ( location instanceof ProgramVariable ) {
                final ProgramVariable pv = (ProgramVariable)location;
                if ( pv.isStatic () )
                    return 1;
                else
                    return 0;
            } else if ( location instanceof AccessOp ) {
                return 2;
            } else
                return 3;
        }
    }
    
    private final static Comparator<ElUpdateLocation> elUpdateComparator =
        new ElUpdateLocationComparator (); 
    
    /**
     * Internal data structure to store all components of an elementary update:
     * bound variables, left-hand side, right-hand side and guard (the guard is
     * here assumed to exist always, i.e. <tt>true</tt> is used as trivial
     * guard).
     * 
     * Two objects are consider equal if and only if the left-hand sides and the
     * guard are equal (modulo bound renaming)
     */
    private static class ElUpdateLocation extends GuardSimplifier {
        private Term lhs;
        private Term value;
        
        // used to make the ordering stable (important because of last-win
        // semantics)
        public final int locationNum;
        
        public ElUpdateLocation (final Term guard,
                                 final ImmutableArray<QuantifiableVariable> boundVars,
                                 final Term lhs,
                                 final Term value,
                                 final int locationNum) {
            super ( guard, boundVars );
            this.lhs = lhs;
            this.value = value;
            this.locationNum = locationNum;
            
            simplify ();
        }
        
        public boolean isTrivialUpdate () {
            return getLhs().equalsModRenaming ( getValue() );
        }
        
        private final static BoundVariableTools bvt = BoundVariableTools.DEFAULT;
        
        public boolean equals (Object o2) {
            if ( !( o2 instanceof ElUpdateLocation ) ) return false;            
            final ElUpdateLocation upd2 = (ElUpdateLocation)o2;
            
            if ( !getLocation ().equals ( upd2.getLocation () ) ) return false;            
            
            return bvt.equalsModRenaming ( getBoundVars (),
                                           getCondition (),
                                           upd2.getBoundVars (),
                                           upd2.getCondition () )
                   && bvt.equalsModRenaming ( getBoundVars (),
                                              getLhs (),
                                              upd2.getBoundVars (),
                                              upd2.getLhs () );
        }
        
        public int hashCode() {
            // we do not know how to compute a hash code for the other
            // components (terms of the left-hand side, condition) that is
            // stable under bound renaming
            // (that is, we are too lazy to implement one)
            return getLocation ().hashCode ();
        }

        public Location getLocation () {
            return (Location)getLhs().op ();
        }

        public Term getLocationSub (int subNum) {
            return getLhs().sub ( subNum );
        }

        public ImmutableArray<QuantifiableVariable> getBoundVars () {
            return getMinimizedVars ();
        }

        public ImmutableSet<QuantifiableVariable> getBoundVarsAsSet () {
            ImmutableSet<QuantifiableVariable> res = DefaultImmutableSet.<QuantifiableVariable>nil();
            for (QuantifiableVariable quantifiableVariable : getMinimizedVars()) res = res.add(quantifiableVariable);
            return res;
        }

        public Term getLhs () {
            return lhs;
        }

        public Term getValue () {
            return value;
        }
        
        protected boolean isNeededVar (QuantifiableVariable var) {
            return getLhs ().freeVars ().contains ( var )
                   || getValue ().freeVars ().contains ( var );
        }
        
        protected void substitute (QuantifiableVariable var, Term substTerm) {
            lhs = subst ( var, substTerm, getLhs () );
            value = subst ( var, substTerm, getValue () );
        }
        
        /**
         * @return a formula that implies that <code>this</code> assignment
         *         subsumes/overrides the assignment <code>loc2</code> (i.e.,
         *         if the formula evaluates to true, then <code>loc2</code> is
         *         overridden by <code>this</code>). The result may contain
         *         some of the variables <code>getBoundVars()</code>, which
         *         are implicitly existentially quantified. One can use the
         *         class <code>GuardSimplifier</code> to check whether the
         *         condition is valid.
         */
        public Term getSubsumptionCondition(ElUpdateLocation loc2) {
            if ( getLocation () != loc2.getLocation ()
                 || getLhs ().javaBlock () != loc2.getLhs ().javaBlock () )
                return tb.ff ();
            
            final Term lhs2 = loc2.anonymiseVariables (
                                   anonymiseVariables ( loc2.getLhs () ) );
         
            Term res = getCondition ();
            for (int i = 0; i != lhs2.arity(); ++i) {
                if ( getLhs ().varsBoundHere ( i ).size () != 0
                     || lhs2.varsBoundHere ( i ).size () != 0 )
                    // in this rather strange situation we don't know what
                    // to do, so we rather be on the safe side and say no
                    return tb.ff ();
                res = tb.and ( res, tb.equals ( getLhs ().sub ( i ),
                                                lhs2.sub ( i ) ) );
            }
            
            return res;
        }

        /**
         * Ensure that none of the variables <code>getBoundVars</code> occurs
         * free in <code>t</code>. This is done by substituting occurring
         * variables with fresh variables
         */
        private Term anonymiseVariables(Term t) {
            if ( t.freeVars ().size () == 0 ) return t;
            
            final ImmutableArray<QuantifiableVariable> oldFreeVars =
                new ImmutableArray<QuantifiableVariable> ( t.freeVars ().
                	toArray (new QuantifiableVariable[t.freeVars().size()]) );
            final QuantifiableVariable[] newFreeVarsTemp =
                new QuantifiableVariable [oldFreeVars.size ()];
            
            bvt.resolveCollisions ( oldFreeVars, newFreeVarsTemp,
                                    getBoundVarsAsSet () );
            
            final ImmutableArray<QuantifiableVariable> newFreeVars =
                new ImmutableArray<QuantifiableVariable> ( newFreeVarsTemp );
            return bvt.renameVariables ( t, oldFreeVars, newFreeVars );
        }
    }
    
    /**
     * Create a term from a list of (quantified, guarded) elementary updates and
     * a target term/formula. The update of the result is optimized as far as
     * possible by sorting the elementary updates, removing unnecessary updates
     * and removing trivial guards. The four array arguments are supposed to
     * have the same size.
     */
    public static Term normalize (ImmutableArray<QuantifiableVariable>[] boundVars,
                                  Term[] guards,
                                  Term[] leftHandSides,
                                  Term[] values,
                                  Term target) {
        final ElUpdateLocation[] normalformOrdering = normalize ( boundVars,
                                                                  guards,
                                                                  leftHandSides,
                                                                  values );

        if (normalformOrdering == null)
            return createTerm ( boundVars, guards, leftHandSides, values, target );

        return normalformOrdering.length == 0 ? 
	    target : createTerm ( normalformOrdering, target );
    }

    /**
     * Create a term from a list of (quantified, guarded) elementary updates and
     * a target term/formula. The only optimisation that is applied at this
     * point is the removal of trivial guards
     */
    private static Term createTerm (ImmutableArray<QuantifiableVariable>[] boundVars,
                                    Term[] guards,
                                    Term[] locations,
                                    Term[] values,
                                    Term target) {
        final boolean[] nontrivialGuards = determineNontrivialGuards ( guards );
        final QuanUpdateOperator op =
            QuanUpdateOperator.createUpdateOp ( locations, nontrivialGuards );

        ImmutableList<Term> resultSubs = ImmutableSLList.<Term>nil().prepend ( target );
        for ( int i = locations.length - 1; i >= 0; i-- ) {
            resultSubs = resultSubs.prepend ( values[i] );
            
            for ( int j = op.location(i).arity () - 1; j >= 0; j-- )
                resultSubs = resultSubs.prepend ( locations[i].sub ( j ) );
            
            if ( nontrivialGuards[i] )
                resultSubs = resultSubs.prepend ( guards[i] );
        }
        
        return tf.createQuanUpdateTermUnordered ( op,
                                                  resultSubs.toArray (new Term[resultSubs.size()]),
                                                  boundVars );
    }

    private static Term createTerm(ElUpdateLocation[] elUpdates,
                                   Term target) {
        final QuanUpdateOperator op =
            QuanUpdateOperator.createUpdateOp ( locations ( elUpdates ),
                                                nontrivialGuards ( elUpdates ) );

        ImmutableList<Term> resultSubs = ImmutableSLList.<Term>nil().prepend ( target );
        for ( int i = elUpdates.length - 1; i >= 0; i-- ) {
            resultSubs = resultSubs.prepend ( elUpdates[i].getValue() );
            
            for ( int j = op.location ( i ).arity () - 1; j >= 0; j-- )
                resultSubs = resultSubs.prepend ( elUpdates[i].getLocationSub ( j ) );
            
            if ( !elUpdates[i].isValidGuard () )
                resultSubs = resultSubs.prepend ( elUpdates[i].getCondition() );
        }
        
        return tf.createQuanUpdateTermUnordered ( op,
                                                  resultSubs.toArray (new Term[resultSubs.size()]),
                                                  boundVars ( elUpdates ) );        
    }
    
    private static ImmutableArray<QuantifiableVariable>[] boundVars (ElUpdateLocation[] elUpdates) {
        final ImmutableArray<QuantifiableVariable>[] res = new ImmutableArray[elUpdates.length];
        for ( int i = 0; i != elUpdates.length; ++i )
            res[i] = elUpdates[i].getBoundVars();
        return res;
    }

    private static Location[] locations (ElUpdateLocation[] elUpdates) {
        final Location[] res = new Location [elUpdates.length];
        for ( int i = 0; i != elUpdates.length; ++i )
            res[i] = elUpdates[i].getLocation ();
        return res;
    }

    private static boolean[] nontrivialGuards (ElUpdateLocation[] elUpdates) {
        final boolean[] res = new boolean [elUpdates.length];
        for ( int i = 0; i != elUpdates.length; ++i )
            res[i] = !elUpdates[i].isValidGuard ();
        return res;
    }

    /**
     * @return a boolean array that contains <code>true</code> in those places
     *         for which <code>guards</code> does not contain the formula
     *         <code>true</code>
     */
    private static boolean[] determineNontrivialGuards (Term[] guards) {
        final boolean[] res = new boolean [guards.length];
        for ( int i = 0; i != guards.length; ++i )
            res[i] = guards[i].op () != Op.TRUE;
        return res;
    }

    /**
     * Given the update operator (<code>this</code>), the variables that are
     * bound and the subterms, create a new term. This applies the same
     * optimisations as
     * <code>normalize (ArrayOf<QuantifiableVariable>[], Term[], Term[], Term[], Term )</code>
     */
    public Term normalize(ImmutableArray<QuantifiableVariable>[] boundVarsPerSub,
                          Term[] subs) {

        // could be implemented more efficiently
        
        final ImmutableArray<QuantifiableVariable>[] boundVars =
            toBoundVarsPerAssignment ( boundVarsPerSub, subs );
        final Term[] guards = new Term [locationCount()];
        final Term[] lhss = new Term [locationCount()];
        final Term[] values = new Term [locationCount()];

        for ( int locNum = 0; locNum != locationCount(); ++locNum ) {
            if ( guardExists ( locNum ) )
                guards[locNum] = subs[guardPos ( locNum )];
            else
                guards[locNum] = getValidGuard();

            final Location loc = location ( locNum );
            final Term[] locSubs = new Term [loc.arity ()];
            System.arraycopy ( subs, locationSubtermsBegin ( locNum ),
                               locSubs, 0,
                               loc.arity () );

            lhss[locNum] = tf.createTerm ( loc,
                                           locSubs,
                                           null,
                                           JavaBlock.EMPTY_JAVABLOCK);
            
            values[locNum] = subs[valuePos ( locNum )];
        }

        final Term target = subs[subs.length - 1];

        return normalize ( boundVars, guards, lhss, values, target );
    }

    /**
     * Determines the ordering of the locations according to the update term
     * normalform and returns an array describing the new order of the
     * locations. Updates with obviously unsatisfiable guards and trivial
     * updates are removed (if possible)
     */
    private static ElUpdateLocation[] normalize (ImmutableArray<QuantifiableVariable>[] boundVars,
                                                 Term[] guards,
                                                 Term[] locations,
                                                 Term[] values) {

        // three sets of assignments, one that is used to order the assignments
        // of an update, one to eliminate those updates that are literally
        // overwritten by later updates, and one to eliminate updates that are
        // subsumed by later quantified updates. The sets are filled
        // "from right to left"
        final TreeSet<ElUpdateLocation> orderedAssignments = 
            new TreeSet<ElUpdateLocation> ( elUpdateComparator );
        final Set<ElUpdateLocation> laterAssignments = new HashSet<ElUpdateLocation> ();
        final List<ElUpdateLocation> laterQuanAssignments = new ArrayList<ElUpdateLocation> ();
        
        for (int locNum = locations.length - 1; locNum >= 0; locNum--) {
            final ElUpdateLocation elUpd =
                new ElUpdateLocation ( guards[locNum],
                                       boundVars[locNum],
                                       locations[locNum],
                                       values[locNum],
                                       locNum );
            if ( elUpd.isUnsatisfiableGuard () ) continue;

            final Location location = elUpd.getLocation ();            
            if ( location instanceof SchemaVariable
                 || location instanceof MetaOperator ) {
                return null;
            }
            
            if ( laterAssignments.contains ( elUpd )
                 || isSubsumedAssignment ( elUpd, laterQuanAssignments ) )
                continue;

            orderedAssignments.add ( elUpd );
            laterAssignments.add ( elUpd );
            
            if ( elUpd.bindsVariables () ) laterQuanAssignments.add ( elUpd );
        }

        final Set<Location> operators = new HashSet<Location> ();
        final Iterator<ElUpdateLocation> it = orderedAssignments.iterator ();
        while ( it.hasNext () ) {
            final ElUpdateLocation elUpd = it.next ();
            final Location loc = elUpd.getLocation ();

            // delete trivial updates (left-hand and right-hand side are
            // equal), but only if there was no predecessing update that
            // could possible cause a clash
            if ( !operators.contains ( loc ) && elUpd.isTrivialUpdate () ) {
                it.remove ();
                continue;
            }
            
            operators.add ( loc );
        }

        return orderedAssignments.toArray
                     ( new ElUpdateLocation[orderedAssignments.size ()] );
    } 

    /**
     * @return <code>true</code> iff the assignment <code>elUpd</code> is
     *         overridden/subsumed by any of the assignments in
     *         <code>laterAssignments</code>. This check in particular works if
     *         <code>laterAssignments</code> contains quantified assignments,
     *         i.e., can detect subsumption in updates like
     *         <code>a[0] := 4 || \for int i; a[i] := 2</code>
     */
    private static boolean isSubsumedAssignment(ElUpdateLocation elUpd,
                                                List<ElUpdateLocation> laterAssignments) {
        for (ElUpdateLocation laterAss : laterAssignments) {
            final Term subsumptionCond = laterAss.getSubsumptionCondition(elUpd);
            final GuardSatisfiabilityFormulaBuilder satisfiabilityBuilder =
                    new GuardSatisfiabilityFormulaBuilder(subsumptionCond,
                            laterAss.getBoundVars());
            if (satisfiabilityBuilder.isValidGuard()) return true;
        }
        return false;
    }
    
    private final static Term validGuardCache = tf.createJunctorTerm ( Op.TRUE );
    private static Term getValidGuard () {
        return validGuardCache;
    }


}
