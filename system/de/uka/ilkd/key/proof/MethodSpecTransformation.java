// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

//
//


package de.uka.ilkd.key.proof;

import java.util.*;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;


/**
 * Transformation according to Sect. 3.3.2 of &quot;Eine modifies-Klausel in
 * KeY&quot; by Bastian Katz
 */
public class MethodSpecTransformation{
    
    private final Term hoare;
    
    /**
     * Maps from <code>Term</code> to <code>LogicVariable</code> describing
     * the flattening of pre and postconditions
     */
    private final Map preFunctions = new HashMap ();
    private final Map postFunctions = new HashMap ();
    
    private final Map logicVariableTerms = new HashMap ();
    private final Map operators = new HashMap ();
    private final Set postsubterms = new HashSet ();

    private final TermFactory tf = TermFactory.DEFAULT;
    
    private void putPreFunction (Term t, LogicVariable var) {
        preFunctions.put ( t, var );
    }
    
    private void putPostFunction (Term t, LogicVariable var) {
        postFunctions.put ( t, var );
    }
    
    private LogicVariable getPreFunctionVar (Term t) {
        return (LogicVariable)preFunctions.get ( t );
    }
    
    private LogicVariable getPostFunctionVar (Term t) {
        return (LogicVariable)postFunctions.get ( t );
    }
    
    private void putOperator (Operator op, Term t) {
        operators.put ( op, t );
    }    
    
    private Term getTermFor (LogicVariable var) {
        Term res = (Term)logicVariableTerms.get ( var );
        if ( res == null ) {
            res = tf.createVariableTerm ( var );
            logicVariableTerms.put ( var, res );
        }
        return res;
    }
    
    private JavaBlock getJavablock () {
        return ( hoare.sub ( 1 ) ).javaBlock ();
    }

    private Term getPostcondition () {
        return hoare.sub ( 1 ).sub ( 0 );
    }

    private Term getPrecondition () {
        return hoare.sub ( 0 );
    }

    public static Term getTransformedHoare (Term hoare) {
        // refactoring "method object"
        return new MethodSpecTransformation ( hoare ).transformHoare ();
    }    

    private MethodSpecTransformation(Term hoare) {
        this.hoare = hoare;
    }

    private Term transformHoare () {
        setupPostSubTerms ( getPostcondition () );
        
        final Term purePrecondition = purifyPrecondition ( getPrecondition () );

        final Set neededTermsLeft = new HashSet ();
        final Set neededTermsRight = new HashSet ();

        // The next three calls are performed only to find out about terms that
        // are needed (update <code>neededTermsLeft</code>,
        // <code>neededTermsRight</code>)
        getConjunction ( preFunctions, neededTermsLeft );
        getConjunction ( postFunctions, neededTermsRight );        
        substitute ( getPostcondition (), neededTermsRight );

        removeUnneededTerms ( neededTermsLeft, neededTermsRight );

        final Term prefix2 = removePres ( getConjunction ( preFunctions,
                                                           neededTermsLeft ) );
        final Term suffix = getConjunction ( postFunctions, neededTermsRight );
        final Term substPostcondition = substitute ( getPostcondition (),
                                                     neededTermsRight );

        // <code>createJunctorTermAndSimplify</code> cannot be used for the
        // following formulas, because the resulting term is expected to have a
        // particular shape
        final Term prefix = tf.createJunctorTerm ( Op.AND,
                                                   purePrecondition,
                                                   prefix2 );
        final Term postImplication = tf.createJunctorTerm ( Op.IMP,
                                                            suffix,
                                                            substPostcondition );        
        final Term diamondTerm = tf.createDiamondTerm ( getJavablock (),
                                                        postImplication );

        Term res = tf.createJunctorTerm ( Op.IMP, prefix, diamondTerm );

        // add necessary quantifiers
        res = addAllQuantifiers ( res, preFunctions.values () );
        res = addAllQuantifiers ( res, postFunctions.values () );
        
        return res;
    }
    
    private Term addAllQuantifiers (Term res, Collection variables) {
        final Iterator it = variables.iterator ();
        while ( it.hasNext () )
            res = tf.createQuantifierTerm ( Op.ALL,
                                            (QuantifiableVariable)it.next (),
                                            res );
        return res;
    }

    private void removeUnneededTerms (Set neededTermsLeft, Set neededTermsRight) {
        final Set remove = new HashSet ();
        findUnneededTerms ( neededTermsLeft, postFunctions, remove );
        findUnneededTerms ( neededTermsRight, preFunctions, remove );

        postFunctions.keySet ().removeAll ( remove );
        preFunctions.keySet ().removeAll ( remove );
    }

    /**
     * Given a set <code>neededVarTerms</code> of variable terms that are
     * needed, determine all related original terms (as given by the mapping
     * <code>termsToVars</code>) and insert them into the collection
     * <code>unneeded</code>
     */
    private void findUnneededTerms (Set neededVarTerms,
                                    Map termsToVars,
                                    Collection unneeded) {
        final Iterator it = termsToVars.entrySet().iterator();
        while(it.hasNext()) {
            final Map.Entry entry = (Map.Entry)it.next ();
            final Term t = (Term)entry.getKey();
            final LogicVariable var = (LogicVariable)entry.getValue();
            if ( !neededVarTerms.contains ( getTermFor ( var ) ) )
                unneeded.add ( t );
        }
    }

    private Term removePres(Term t) {
        checkForBoundVariables ( t );
        
	Term[] subs = new Term [t.arity ()];
        boolean changed = false;
        for ( int i = 0; i < subs.length; i++ ) {
            subs[i] = removePres ( t.sub ( i ) );
            if ( subs[i] != t.sub ( i ) ) changed = true;
        }
    
	if ( operators.containsKey ( t.op () ) ) {
            t = (Term)operators.get ( t.op () );
            if ( t.op () instanceof AttributeOp )
                subs = new Term [] { subs[0] };
            changed = true;
        }
    
	if ( changed ) return buildTerm ( t.op (), subs, t.javaBlock () );

        return t;
    }
    
    private Term substitute (Term from, Set notifyUsage) {
        
        // test if term <code>from</code> is contained in one of the mappings;
        // in this case return the variable the term is mapped to
        LogicVariable varForFrom = getPreFunctionVar ( from );
        if ( varForFrom == null ) varForFrom = getPostFunctionVar ( from );
        if ( varForFrom != null ) {
            final Term t = getTermFor ( varForFrom );
            notifyUsage.add ( t );
            return t;
        }

        checkForBoundVariables ( from );
        
        final BooleanContainer changed = new BooleanContainer ();
        final Term subTerms[] = substituteSubterms ( from, notifyUsage, changed );
        
	Operator top = from.op ();
        if ( operators.containsKey ( top ) ) {
            top = ( (Term)operators.get ( top ) ).op ();
            changed.setVal ( true );
        }
	
	if ( changed.val () )
	    return buildTerm ( top, subTerms, from.javaBlock () );
        return from;
    }

    private void checkForBoundVariables (Term t) {
        for ( int i = 0; i != t.arity (); ++i )
            Debug.assertTrue ( t.varsBoundHere ( i ).size () == 0,
                               "MethodSpecTransformation does not support "
                               + "quantifiers at this point!\n"
                               + "Term " + t + " cannot be handled" );
    }

    /**
     * Given a mapping <code>termsToVars</code> of terms to variables, create
     * a conjunction of equations <code>x=t</code>, where <code>t</code> is
     * obtained by replacing the direct subterms of a term of the mapping with
     * the related variables
     */
    private Term getConjunction (Map termsToVars,
                                 Set needed) {	
        Term result = tf.createJunctorTerm ( Op.TRUE );

        final Iterator it = termsToVars.entrySet ().iterator ();        
        while ( it.hasNext () ) {
            final Map.Entry entry = (Map.Entry)it.next ();
            final Term term = (Term)entry.getKey ();
            final Term varTerm = getTermFor ( (LogicVariable)entry.getValue () );

            needed.add ( varTerm );
            final Term changedMap = tf.createTerm ( term.op (),
                                                    substituteSubterms ( term,
                                                                         needed,
                                                                         null ),
                                                    new QuantifiableVariable [0],
                                                    term.javaBlock () );            
            final Term resPart = tf.createEqualityTerm ( varTerm,
                                                         changedMap );
            
            result = tf.createJunctorTermAndSimplify ( Op.AND, result, resPart );
        }
	
	return result;
    }

    /**
     * Invoke the method <code>substitute</code> on all direct subterms of
     * <code>term</code>
     * 
     * @param changed
     *            if a non-null boolean container is given, store
     *            <code>true</code> iff one of the subterms was changed by the
     *            invocation
     */
    private Term[] substituteSubterms (Term term,
                                       Set needed,
                                       BooleanContainer changed) {
        if ( changed != null ) changed.setVal ( false );
        final Term[] subTerms = new Term [term.arity ()];
        for ( int i = 0; i < term.arity (); i++ ) {
            subTerms[i] = substitute ( term.sub ( i ),
                                       needed );
            if ( changed != null && !subTerms[i].equals ( term.sub ( i ) ) )
                changed.setVal ( true );
        }
        return subTerms;
    }

    /**
     * Store all subterms of <code>t</code> in the attribute
     * <code>postsubterms</code>
     * 
     * @param t
     *            Term whose subterms are supposed to be determined
     */
    private void setupPostSubTerms (Term t) {
        if ( !postsubterms.contains ( t ) ) {
            postsubterms.add ( t );

            if ( t.sort () != Sort.FORMULA ) {
                final LogicVariable subst = new LogicVariable ( new Name ( "_tauV"
                                                                           + postsubterms.size () ),
                                                                t.sort () );

                if ( opIsAtPre ( t ) )
                    putPreFunction ( t, subst );
                else
                    putPostFunction ( t, subst );
            }

            for ( int i = 0; i < t.arity (); i++ )
                setupPostSubTerms ( t.sub ( i ) );
        }
    }

    public static boolean opIsAtPre (Term t) {
        return t.op () instanceof Function
               && ( (Function)t.op () ).name ().toString ().indexOf ( "@pre" ) > -1;
    }

    public static boolean isAtPreDefinition (final Term pre) {
        return pre.op () == Op.ALL
                 && pre.sub ( 0 ).op () instanceof de.uka.ilkd.key.logic.op.Equality
                 && opIsAtPre ( pre.sub ( 0 ).sub ( 0 ) );
    }

    /**
     * Remove premisses defining the helper functions for
     * @pre from the precondition
     */
    private Term purifyPrecondition(final Term pre){
	if ( isAtPreDefinition ( pre ) ) {
	    // replace formulas
	    //               all x. f@pre(...) = t
	    // with TRUE
            putOperator ( pre.sub ( 0 ).sub ( 0 ).op (), pre.sub ( 0 ).sub ( 1 ) );
            return tf.createJunctorTerm ( Op.TRUE );
        }
	
	checkForBoundVariables ( pre );

	boolean changed = false;
        final Term subTerms[] = new Term [pre.arity ()];
        for ( int i = 0; i < pre.arity (); i++ ) {
            subTerms[i] = purifyPrecondition ( pre.sub ( i ) );
            if ( !subTerms[i].equals ( pre.sub ( i ) ) ) changed = true;
        }
        
        if ( changed )
            return buildTerm ( pre.op (), subTerms, pre.javaBlock () );

        return pre;    
    }

    private final static ArrayOfQuantifiableVariable EMPTY_ARRAY_OF_VARIABLES =
        new ArrayOfQuantifiableVariable ();
    
    private Term buildTerm (Operator op,
                            Term[] subTerms,
                            JavaBlock javaBlock) {
        if ( op instanceof Junctor && subTerms.length == 2 )
            return tf.createJunctorTermAndSimplify ( (Junctor)op,
                                                     subTerms[0],
                                                     subTerms[1] );
        return tf.createTerm ( op,
                               subTerms,
                               EMPTY_ARRAY_OF_VARIABLES,
                               javaBlock);
    }
}
