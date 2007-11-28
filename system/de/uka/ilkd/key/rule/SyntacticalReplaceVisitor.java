// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


/**
 * visitor for <t> execPostOrder </t> of 
 * {@link de.uka.ilkd.key.logic.Term}. Called with that method
 * on a term, the visitor builds a new term replacing SchemaVariables with their
 * instantiations that are given as a SVInstantiations object.
 */
package de.uka.ilkd.key.rule;

import java.util.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.java.visitor.ProgramReplaceVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;
import de.uka.ilkd.key.rule.inst.ContextInstantiationEntry;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

public class SyntacticalReplaceVisitor extends Visitor { 	

    private final SVInstantiations svInst;
    private final Constraint metavariableInst;
    private MapFromSchemaVariableToTerm newInstantiations =
                                MapAsListFromSchemaVariableToTerm.EMPTY_MAP;
    private final boolean forceSVInst;
    private final Name svInstBasename;
    private Services services;
    private Term computedResult = null;
    private TypeConverter typeConverter = null;
    private final boolean allowPartialReplacement;
    private final boolean resolveSubsts;

    /**
     * the stack contains the subterms that will be added in the next step of
     * execPostOrder in Term in order to build the new term. A boolean value
     * between or under the subterms on the stack indicate that a term using
     * these subterms should build a new term instead of using the old one,
     * because one of its subterms has been built, too.
     */
    private final Stack subStack; //of Term (and Boolean)
    private final TermFactory tf = TermFactory.DEFAULT;
    private final Boolean newMarker = new Boolean(true);
    
    /** used to indicate if variables have changed */
    private final BooleanContainer varsChanged = new BooleanContainer();
    
    /** an empty array for resourse optimisation*/
    private static final 
      QuantifiableVariable[] EMPTY_QUANTIFIABLE_VARS = new QuantifiableVariable[0];


    /**
     * @param forceSVInst iff true instantiate uninstantiated SVs by
     * creating new metavariables or new bound logicvariables
     */
    public SyntacticalReplaceVisitor(Services              services, 
				     SVInstantiations      svInst,
				     Constraint            metavariableInst,
				     boolean               forceSVInst,

				     Name                  svInstBasename,
				     boolean               allowPartialReplacement,
				     boolean               resolveSubsts) { 
	this.services         = services;	
	this.svInst           = svInst;
	this.metavariableInst = metavariableInst;
	this.forceSVInst      = forceSVInst;
	this.svInstBasename   = svInstBasename;
	this.allowPartialReplacement = allowPartialReplacement;
	this.resolveSubsts    = resolveSubsts;
	subStack = new Stack(); // of Term
    }

    public SyntacticalReplaceVisitor(Services              services, 
				     SVInstantiations      svInst,
				     Constraint            metavariableInst,
				     boolean               forceSVInst,
				     Name                  svInstBasename) {
	this ( services, 
	       svInst,
	       metavariableInst,
	       forceSVInst,
	       svInstBasename,
	       false, true );
    }

    public SyntacticalReplaceVisitor(Services services, 
				     SVInstantiations svInst) { 
	this ( services, svInst, Constraint.BOTTOM, false, null, false, true );
    }

    public SyntacticalReplaceVisitor(Services services, 
				     Constraint metavariableInst) { 
	this ( services,
	       SVInstantiations.EMPTY_SVINSTANTIATIONS,
	       metavariableInst, 
	       false, null, false, true );
    }

    public SyntacticalReplaceVisitor(Services services, 
                                     SVInstantiations svInst,
                                     Constraint metavariableInst) { 
        this ( services, svInst, metavariableInst, false, null, false, true );
    }

    public SyntacticalReplaceVisitor(Constraint metavariableInst) { 
	this ( null, metavariableInst );
    }

    private JavaProgramElement addContext(StatementBlock pe) {
	final ContextInstantiationEntry cie = 
	    svInst.getContextInstantiation();
	if (cie == null) {
	    throw new IllegalStateException("Context should also "
					    +"be instantiated");
	}	

	if (cie.prefix() != null) {
	    return ProgramContextAdder.INSTANCE.start
		((JavaNonTerminalProgramElement)cie.contextProgram(), 
		 pe,
		 (ContextStatementBlockInstantiation)cie.getInstantiation());
	} 

	return pe;
    }

    private Services getServices () {
	if ( services == null )
	    services = new Services ();
	return services;
    }

    private TypeConverter getTypeConverter () {
	if ( typeConverter == null )
	    typeConverter = getServices ().getTypeConverter();
	return typeConverter;
    }

    private JavaBlock replacePrg(SVInstantiations svInst, JavaBlock jb) {
	if ( svInst == SVInstantiations.EMPTY_SVINSTANTIATIONS ) {
	    return jb;
	}
	ProgramReplaceVisitor trans;
	ProgramElement result = null;

	if (jb.program() instanceof ContextStatementBlock) {
	    trans = new ProgramReplaceVisitor
		(new StatementBlock(((ContextStatementBlock)jb.program()).getBody()), // TODO
		 getServices (),
		 svInst,
		 allowPartialReplacement);
	    trans.start();
	    result = addContext((StatementBlock)trans.result());
	} else {
	    trans = new ProgramReplaceVisitor(jb.program(),
					      getServices (),
					      svInst,
					      allowPartialReplacement);
	    trans.start();
	    result = trans.result();
	}
	return (result==jb.program()) ? 
            jb : JavaBlock.createJavaBlock((StatementBlock)result);
    }

    private Term[] neededSubs(int n) {
	boolean newTerm = false;
	Term[] result   = new Term[n];
	for (int i = n-1; i >= 0; i--) {
	    Object top = subStack.pop();
	    if (top == newMarker){
		newTerm = true; 
		top     = subStack.pop();
	    }
	    result[i] = (Term) top;
	}
	if (newTerm && (subStack.empty() || 
			subStack.peek() != newMarker) ) {
	    subStack.push(newMarker);
	}
	return result;
    }

    /**
     * Pop the top-most <code>n</code> objects from the subterm stack,
     * together with possibly interleaving newmarkers, store everything in
     * <code>store</code>. The top element of the stack will be the last
     * element of list <code>store</code>
     */
    private void popN (int n, LinkedList store) {
        for ( int i = 0; i < n; i++ ) {
            store.addFirst ( subStack.pop () );
            if ( subStack.peek () == newMarker ) {
                store.addFirst ( subStack.pop () );
            }
        }
    }

    /**
     * Push the given objects on the subterm stack, in the order in which they
     * are returned by the method <code>iterator</code>
     */
    private void push (Collection store) {
        final Iterator it = store.iterator ();
        while ( it.hasNext () )
            subStack.push ( it.next () );
    }

    private void pushNew(Object t) {
	if (subStack.empty() || subStack.peek() != newMarker) {
	    subStack.push(newMarker);
	}
	subStack.push(t);	
    }

    
    private void pushNewAt(Object[] t, int posFromTop) {

	final LinkedList store = new LinkedList();
	popN ( posFromTop, store );

	for (int i = 0; i<t.length; i++) {
	    pushNew(t[i]);	
	}

        push ( store );
    }


    private void replaceAt (Object[] t, int posFromTop, int length) {

	final LinkedList store = new LinkedList();
	popN ( posFromTop, store );

	// remove 
	popN ( length, new LinkedList () );

	// add new 
	for (int i = 0; i<t.length; i++) {	    
	    pushNew(t[i]);	
	}

        push ( store );
    }


    private Term[] peek(int pos, int length) {

	final Term[] result = new Term[length];

	final LinkedList store = new LinkedList();
	popN ( pos + length, store );

	final Iterator it = store.iterator ();
        for ( int i = 0; i < length; i++ ) {
            Object o = it.next ();
            if ( o == newMarker ) o = it.next ();
            result[i] = (Term)o;
        }

        push ( store );

	return result;
    }

    private Term toTerm(Object o) {
	if (o instanceof Term) {
	    final Term t = (Term)o;
            if ( t.metaVars ().size () != 0 && !metavariableInst.isBottom () ) {
                // use the visitor recursively for replacing metavariables that
                // might occur in the term (if possible)
                final SyntacticalReplaceVisitor srv =
                    new SyntacticalReplaceVisitor ( metavariableInst );
                t.execPostOrder ( srv );
                return srv.getTerm ();
            }
            return t;
	} else if (o instanceof ProgramElement) {	    
	    ExecutionContext ec
		= (svInst.getContextInstantiation()==null)
		? null 
		: svInst.getContextInstantiation()
		               .activeStatementContext();
	    return getTypeConverter().
		convertToLogicElement((ProgramElement)o, ec);
	}
        de.uka.ilkd.key.util.Debug.fail("Wrong instantiation in SRVisitor");
	return null;
    }

    private void updateLocation (Location loc,
                                 Term location,
                                 int positionInStack,
                                 int oldLocationArity,
                                 boolean replace) {
        final Term[] newSubterms = new Term [loc.arity ()];
        for ( int j = 0; j < newSubterms.length; j++ ) {
            newSubterms[j] = location.sub ( j );
        }
        if ( replace ) {
            replaceAt ( newSubterms, positionInStack, oldLocationArity );
        } else {
            pushNewAt ( newSubterms, positionInStack );
        }
    }


    private IUpdateOperator instantiateUpdateOperator(IUpdateOperator op) {
	final Location[] newOps = new Location[op.locationCount()];	
	final int locCount      = op.locationCount();	
	boolean changed = false;	    	    
	for (int i = 0; i < locCount; i++) {	    
	    final Location originalOp = op.location(i);	    
	    if (originalOp instanceof SchemaVariable) {
		final Object inst = svInst.getInstantiation
		    ((SchemaVariable)originalOp);
		if (!(inst instanceof Operator)) {
		    if (inst == null) {
		        // we have only a partial instantiation
		        // continue with schema
		        newOps[i] = originalOp;
		    } else {                
		        final int posInStack = op.arity() - op.locationSubtermsEnd(i);
		        Term instantiation = toTerm(inst);
		        newOps[i] = (Location)instantiation.op();
		        updateLocation(newOps[i], instantiation, 
		                posInStack, 0, false);
		    }
		} else {
		    newOps[i] = (Location) inst;
		}
	    } else if (originalOp instanceof MetaOperator) {
		final MetaOperator mop = (MetaOperator) originalOp;		
		final int posInStack = op.arity() - op.locationSubtermsEnd(i);

		final Term computedLocation =
		    mop.calculate(tf.createMetaTerm(mop,
		                                    peek(posInStack, mop.arity())), 
		                                    svInst, getServices());		
		newOps[i] = (Location) computedLocation.op();

		updateLocation(newOps[i], computedLocation, posInStack, 
			       mop.arity(), true);
	    } else {
                if (originalOp instanceof ArrayOp) {
                    final int posInStack = op.arity() - op.locationSubtermsEnd(i);
                    newOps[i] = (Location) instantiateArrayOperator((ArrayOp) originalOp, posInStack);
                } else {
                    newOps[i] = (Location) instantiateOperator(originalOp);
                }
	    }	   
	    changed = (changed || (newOps[i] != originalOp));
	}		

	if ( !changed ) return op;

	return op.replaceLocations ( newOps );
    }

  

    private AttributeOp instantiateAttributeOperator(AttributeOp op) {
        if (op.attribute() instanceof SchemaVariable) {
            final IProgramVariable attribute = 
                (ProgramVariable)svInst.getInstantiation
                ((SchemaVariable)op.attribute());   
            if (attribute == null) {
                // illegal inst. exception required for matchMV to fail
                throw new IllegalInstantiationException
                ("No instantiation found for " + op);
            }
            
            if (op instanceof ShadowedOperator) {
                op = ShadowAttributeOp.getShadowAttributeOp(attribute);
            } else {
                op = AttributeOp.getAttributeOp(attribute);
            }
        }
        return op;
    }
    
    private ArrayOp instantiateArrayOperator(ArrayOp op, int pos) {       
        final Sort sortDependingOn = op.getSortDependingOn();
        final Sort s;
        if (sortDependingOn == null) {
            s = peek(pos, op.arity())[0].sort();
        } else if (sortDependingOn instanceof GenericSort) {
            s = svInst.getGenericSortInstantiations().
                getInstantiation((GenericSort) sortDependingOn);
        } else {
            return op;
        }       
        assert s instanceof ArraySort : "Expected array sort but is " + s;
        return op instanceof ShadowedOperator ? 
                ShadowArrayOp.getShadowArrayOp(s) : ArrayOp.getArrayOp(s);        

    }
    
    private Operator instantiateOperatorSV(OperatorSV op) {
        Operator newOp = (Operator) svInst.getInstantiation(op);
        Debug.assertTrue(newOp != null, "No instantiation found for " + op);
        return newOp;
    }

    private Operator instantiateOperator(Operator op) {	
	if (op instanceof OperatorSV){	 
            return instantiateOperatorSV((OperatorSV) op);
        } else if (op instanceof AttributeOp) {
	    return instantiateAttributeOperator((AttributeOp)op);
	} else if (op instanceof ArrayOp) {
	    return instantiateArrayOperator((ArrayOp)op, 0);
        } else if (op instanceof SortDependingSymbol) {
            return handleSortDependingSymbol(op);
        } else if (op instanceof IUpdateOperator) {        
	    return instantiateUpdateOperator((IUpdateOperator)op);       
	} else if (op instanceof NRFunctionWithExplicitDependencies) { 
	    return instantiateNRFunctionWithExplicitDependencies
	    	((NRFunctionWithExplicitDependencies)op);
	} else if (op instanceof SortedSchemaVariable &&
                    ((SortedSchemaVariable)op).isListSV()){
            return op;
        } else if (op instanceof SortedSchemaVariable) {
	    return (Operator)svInst.getInstantiation((SchemaVariable)op);
	} 
	return op;
    }

    /**
     * @param dependencies
     * @return
     */
    private Operator instantiateNRFunctionWithExplicitDependencies
    	(NRFunctionWithExplicitDependencies nrFunc) {
        final Location[] locs = new Location[nrFunc.dependencies().size()];
        final ArrayOfLocation patternDeps = nrFunc.dependencies();
        boolean instantiationNecessary = false;
        for (int i = 0; i<locs.length; i++) {
            Location loc = patternDeps.getLocation(i);            
            if (loc instanceof SchemaVariable) {                
                Object o = svInst.getInstantiation((SchemaVariable)loc); 
                if (o instanceof Term) {
                    loc =(Location) ((Term)o).op();
                } else {
                    Debug.assertTrue(o instanceof Location);
                    loc = (Location)o;
                }
                instantiationNecessary = true;
            }
            locs[i] = loc;
        }
        
        if (!instantiationNecessary) return nrFunc;
        
        // HACK
        String name = nrFunc.name().toString();
        name = name.substring(0, name.indexOf("[")+1);
        for (int i = 0; i<locs.length; i++) {
            name += locs[i].name();
            name += ";";
        }
        name += "]";
        return NRFunctionWithExplicitDependencies.
        	getSymbol(new Name(name), new ArrayOfLocation(locs));
    }
    
    private ArrayOfQuantifiableVariable[] instantiateBoundVariables(Term visited) {
        boolean containsBoundVars = false;
        ArrayOfQuantifiableVariable[] boundVars = 
            new ArrayOfQuantifiableVariable[visited.arity()];

        for (int i = 0, arity = visited.arity(); i < arity; i++) {
            final ArrayOfQuantifiableVariable vBoundVars =
                visited.varsBoundHere(i);
        
            final QuantifiableVariable[] newVars = (vBoundVars.size() > 0)? 
                    new QuantifiableVariable[vBoundVars.size()]
                    : EMPTY_QUANTIFIABLE_VARS;
                    
            for (int j = 0, size = vBoundVars.size(); j < size; j++) {                 
                containsBoundVars = true;
                QuantifiableVariable boundVar = vBoundVars.getQuantifiableVariable(j);
                if (boundVar instanceof SchemaVariable) {
                    final SortedSchemaVariable boundSchemaVariable = 
                        (SortedSchemaVariable) boundVar;
                    if (svInst.isInstantiated(boundSchemaVariable)) {
                        boundVar = ((QuantifiableVariable) ((Term) svInst
                                .getInstantiation(boundSchemaVariable))
                                .op());
                    } else {
                        if (forceSVInst) {
                            boundVar = createTemporaryLV(boundSchemaVariable);
                        } else {
                            // this case may happen for PO generation of
                            // taclets
                            boundVar = boundSchemaVariable;
                        }
                    }
                    varsChanged.setVal(true);
                } 
                newVars[j] = boundVar;                    
            }
            boundVars[i] =  varsChanged.val() ?                     
                    new ArrayOfQuantifiableVariable(newVars) : vBoundVars;                
        }           
        
        if (!containsBoundVars) {
            boundVars = null;
        }
        return boundVars;
    }
    

    public void visit(Term visited) {
        // Sort equality has to be ensured before calling this method
        final Operator visitedOp = visited.op();
        if (visitedOp instanceof SortedSchemaVariable
                && svInst.isInstantiated((SchemaVariable) visitedOp)
                && (!((SchemaVariable) visitedOp).isListSV())) {
            pushNew(toTerm(svInst.getInstantiation((SchemaVariable) visitedOp)));
        } else if (forceSVInst && visitedOp instanceof SortedSchemaVariable
                && ((SchemaVariable) visitedOp).isTermSV()
                && instantiateWithMV(visited)) {
            // then we are done ...
        } else if ((visitedOp instanceof Metavariable)
                && metavariableInst.getInstantiation((Metavariable) visitedOp) != visitedOp) {
            pushNew(metavariableInst.getInstantiation((Metavariable) visitedOp));
        } else if (visitedOp instanceof ExpressionOperator) {
            ExpressionOperator exprOp = (ExpressionOperator) visitedOp;
            pushNew(exprOp.resolveExpression(svInst, getServices()));
        } else {
           
            Operator newOp = instantiateOperator(visitedOp);

            if (newOp == null) {
                // only partial instantiation information available
                // use original op
                newOp = visitedOp;
            }

            boolean operatorInst = (newOp != visitedOp);
            

            // instantiation of java block
            boolean jblockChanged = false;
            JavaBlock jb = visited.javaBlock();

            if (jb != JavaBlock.EMPTY_JAVABLOCK) {
                jb = replacePrg(svInst, jb);
                if (jb != visited.javaBlock()) {
                    jblockChanged = true;
                }
            }
            
           // instantiate bound variables            
           varsChanged.setVal(false); // reset variable change flag
           final ArrayOfQuantifiableVariable[] boundVars = 
               instantiateBoundVariables(visited);
            
            Term[] neededsubs = neededSubs(newOp.arity());
            if (varsChanged.val() || jblockChanged || operatorInst
                    || (!subStack.empty() && subStack.peek() == newMarker)) {
                pushNew(resolveSubst(tf.createTerm(newOp, neededsubs, boundVars,
                        jb)));
            } else {
                final Term t = resolveSubst(visited);
                if (t == visited)
                    subStack.push(t);
                else
                    pushNew(t);
            }
        }
    }
    
    /**
     * @param boundSchemaVariable
     * @return
     */
    private LogicVariable createTemporaryLV (SortedSchemaVariable boundSchemaVariable) {
        final Term t = newInstantiations.get ( boundSchemaVariable );
        if ( t != null ) return (LogicVariable)t.op ();
        
        final Sort realSort = svInst.getGenericSortInstantiations ()
                                .getRealSort ( boundSchemaVariable.sort (), getServices() );
        final LogicVariable v = new LogicVariable ( new Name ( "TempLV" ),
                                                    realSort );
        
        newInstantiations = newInstantiations.put ( boundSchemaVariable,
                                                    tf.createVariableTerm ( v ) );
        return v;
    }

    private Operator handleSortDependingSymbol (Operator op) {
        final SortDependingSymbol depOp = (SortDependingSymbol)op;
        final Sort depSort = depOp.getSortDependingOn ();
        
        
        
        final SortDefiningSymbols realDepSort =
            (SortDefiningSymbols)svInst.getGenericSortInstantiations ()
                                       .getRealSort ( depSort, getServices() );
        
        
        final Operator res = (Operator)depOp.getInstanceFor ( realDepSort );
        Debug.assertFalse ( res == null,
                            "Did not find instance of symbol "
                            + op + " for sort " + realDepSort );
        return res;
    }

    private Term resolveSubst(Term t) {
	if (resolveSubsts && t.op() instanceof SubstOp)
	    return ((SubstOp)t.op ()).apply ( t );
	return t;
    }


    /**
     * PRECONDITION: visited.op() instanceof SchemaVariable &&
     *               ((SchemaVariable)visited.op()).isTermSV ()
     * Instantiate the given TermSV with a new metavariable
     * @return true iff the instantiation succeeded
     */
    private boolean instantiateWithMV ( Term visited ) {
	if ( newInstantiations == null ) return false;

	final SchemaVariable sv = (SchemaVariable)visited.op ();

	Term t = newInstantiations.get ( sv );

	if ( t == null ) {
	    final Sort realSort = svInst.getGenericSortInstantiations ()
	                                .getRealSort ( visited.sort (), getServices() );
            final Metavariable mv = MetavariableDeliverer.createNewMatchVariable
                                        ( svInstBasename.toString (), realSort, getServices() );

            if ( mv == null ) {
                newInstantiations = null;
                return false;
            } else {
                t = tf.createFunctionTerm ( mv );
                newInstantiations = newInstantiations.put ( sv, t );
            }
        }

	pushNew ( t );
	return true;
    }

    /**
     * delivers the new built term
     */
    public Term getTerm() {
	if (computedResult==null) {
	    Object o=null;
	    do {
		o=subStack.pop();
	    } while (o==newMarker);
	    Term t = (Term) o;
// 	    CollisionDeletingSubstitutionTermApplier substVisit
// 		= new CollisionDeletingSubstitutionTermApplier();
// 	    t.execPostOrder(substVisit);	    
// 	    t=substVisit.getTerm();	
	    computedResult=t;
	}	
	return computedResult;
    }


    public SVInstantiations getSVInstantiations () {
	return svInst;
    }


    /**
     * @return introduced metavariables for instantiation of schema
     * variables, or null if some schema variables could not be
     * instantiated
     */
    public MapFromSchemaVariableToTerm getNewInstantiations () {
	return newInstantiations;
    }



    /**
     * this method is called in execPreOrder and execPostOrder in class Term
     * when leaving the subtree rooted in the term subtreeRoot.
     * Default implementation is to do nothing. Subclasses can
     * override this method 
     * when the visitor behaviour depends on informations bound to subtrees.
     * @param subtreeRoot root of the subtree which the visitor leaves.
     */
    public void subtreeLeft(Term subtreeRoot){
	if (subtreeRoot.op() instanceof MetaOperator) {
	    MetaOperator mop = (MetaOperator) subtreeRoot.op();
	    pushNew(mop.calculate((Term)subStack.pop(),svInst, getServices()));
	} 
   }


}
