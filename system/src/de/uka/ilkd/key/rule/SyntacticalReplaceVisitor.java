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


/**
 * visitor for <t> execPostOrder </t> of
 * {@link de.uka.ilkd.key.logic.Term}. Called with that method
 * on a term, the visitor builds a new term replacing SchemaVariables with their
 * instantiations that are given as a SVInstantiations object.
 */
package de.uka.ilkd.key.rule;

import java.util.Stack;

import de.uka.ilkd.key.collection.DefaultImmutableMap;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.java.visitor.ProgramReplaceVisitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SubstOp;
import de.uka.ilkd.key.logic.op.TermTransformer;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.ContextInstantiationEntry;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Constraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EqualityConstraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable;
import de.uka.ilkd.key.util.Debug;

public final class SyntacticalReplaceVisitor extends DefaultVisitor {

    private final SVInstantiations svInst;
    @Deprecated
    private final Constraint metavariableInst;
    private ImmutableMap<SchemaVariable,Term> newInstantiations =
                                DefaultImmutableMap.<SchemaVariable,Term>nilMap();
    private Services services;
    private Term computedResult = null;
    private TypeConverter typeConverter = null;
    private final boolean allowPartialReplacement;
    private final boolean resolveSubsts;
    private final PosInOccurrence applicationPosInOccurrence;
    private final Rule rule;

    /**
     * the stack contains the subterms that will be added in the next step of
     * execPostOrder in Term in order to build the new term. A boolean value
     * between or under the subterms on the stack indicate that a term using
     * these subterms should build a new term instead of using the old one,
     * because one of its subterms has been built, too.
     */
    private final Stack<Object> subStack; //of Term (and Boolean)
    private final TermFactory tf = TermFactory.DEFAULT;
    private final Boolean newMarker = new Boolean(true);

    /** an empty array for resource optimisation*/
    private static final
      QuantifiableVariable[] EMPTY_QUANTIFIABLE_VARS = new QuantifiableVariable[0];


    /**
     */
    public SyntacticalReplaceVisitor(Services services,
                                     SVInstantiations svInst,
                                     PosInOccurrence applicationPosInOccurrence,
                                     Rule rule,
                                     Constraint metavariableInst,
                                     boolean allowPartialReplacement,
                                     boolean  resolveSubsts) {
	this.services         = services;	
	this.svInst           = svInst;
	this.metavariableInst = metavariableInst;
	this.allowPartialReplacement = allowPartialReplacement;
	this.resolveSubsts    = resolveSubsts;
	this.applicationPosInOccurrence = applicationPosInOccurrence;
	this.rule = rule;
	subStack = new Stack<Object>(); // of Term
    }

    public SyntacticalReplaceVisitor(Services services,
                                     SVInstantiations svInst,
                                     PosInOccurrence applicationPosInOccurrence,
                                     Rule rule) {
       this(services, svInst, applicationPosInOccurrence, rule, Constraint.BOTTOM, false, true);
    }

    public SyntacticalReplaceVisitor(Services services,
                                     Constraint metavariableInst,
                                     PosInOccurrence applicationPosInOccurrence,
                                     Rule rule) {
       this(services,
            SVInstantiations.EMPTY_SVINSTANTIATIONS,
            applicationPosInOccurrence,
            rule,
            metavariableInst, 
            false, 
            true);
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
       return services;
    }

    private TypeConverter getTypeConverter () {
	if ( typeConverter == null )
	    typeConverter = getServices ().getTypeConverter();
	return typeConverter;
    }

    private JavaBlock replacePrg(SVInstantiations svInst, JavaBlock jb) {
        if ( svInst.isEmpty() ) {
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


    private void pushNew(Object t) {
	if (subStack.empty() || subStack.peek() != newMarker) {
	    subStack.push(newMarker);
	}
	subStack.push(t);
    }

    private Term toTerm(Object o) {
	if (o instanceof Term) {
	    final Term t = (Term)o;
            if ( EqualityConstraint.metaVars (t).size () != 0 && !metavariableInst.isBottom () ) {
                // use the visitor recursively for replacing metavariables that
                // might occur in the term (if possible)
                final SyntacticalReplaceVisitor srv =
                    new SyntacticalReplaceVisitor (getServices(), metavariableInst, applicationPosInOccurrence, rule);
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
        de.uka.ilkd.key.util.Debug.fail("Wrong instantiation in SRVisitor: " + o);
	return null;
    }


    private Term elementaryUpdateLhs; //HACK
    private ElementaryUpdate instantiateElementaryUpdate(ElementaryUpdate op) {
	elementaryUpdateLhs = null;
	final UpdateableOperator originalLhs = op.lhs();
	if(!(originalLhs instanceof SchemaVariable)) {
	    return op;
	}

	final Object lhsInst
		= svInst.getInstantiation((SchemaVariable) originalLhs);
	final UpdateableOperator newLhs;
	if(lhsInst instanceof UpdateableOperator) {
	    newLhs = (UpdateableOperator) lhsInst;
	} else if(lhsInst == null) {
	    // we have only a partial instantiation
	    // continue with schema
	    newLhs = originalLhs;
	} else {
	    Term termInst = toTerm(lhsInst);
	    HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	    if(termInst.op() instanceof UpdateableOperator) {
		newLhs = (UpdateableOperator)termInst.op();
	    } else if(heapLDT.getSortOfSelect(termInst.op()) != null
		    && termInst.sub(0).op().equals(heapLDT.getHeap())) {
		newLhs = (LocationVariable) termInst.sub(0).op();
		elementaryUpdateLhs = termInst;
	    } else {
		assert false : "not updateable: " + termInst;
	    	newLhs = null;
	    }
	}

	return newLhs == originalLhs
	       ? op
	       : ElementaryUpdate.getInstance(newLhs);
    }


    private Operator instantiateOperatorSV(ModalOperatorSV op) {
        Operator newOp = (Operator) svInst.getInstantiation(op);
        Debug.assertTrue(newOp != null, "No instantiation found for " + op);
        return newOp;
    }

    private Operator instantiateOperator(Operator op) {
	if (op instanceof ModalOperatorSV){
            return instantiateOperatorSV((ModalOperatorSV) op);
        } else if (op instanceof SortDependingFunction) {
            return handleSortDependingSymbol((SortDependingFunction)op);
        } else if (op instanceof ElementaryUpdate) {
	    return instantiateElementaryUpdate((ElementaryUpdate)op);
	}  else if (op instanceof ProgramSV && ((ProgramSV)op).isListSV()){
            return op;
        } else if (op instanceof SchemaVariable) {
	    return (Operator)svInst.getInstantiation((SchemaVariable)op);
	}
	return op;
    }

    private ImmutableArray<QuantifiableVariable> instantiateBoundVariables(Term visited) {
        final ImmutableArray<QuantifiableVariable> vBoundVars = visited.boundVars();
        final QuantifiableVariable[] newVars = (vBoundVars.size() > 0)?
        	new QuantifiableVariable[vBoundVars.size()]
        	                         : EMPTY_QUANTIFIABLE_VARS;
        boolean varsChanged = false;

        for(int j = 0, size = vBoundVars.size(); j < size; j++) {
            QuantifiableVariable boundVar = vBoundVars.get(j);
            if (boundVar instanceof SchemaVariable) {
        	final SchemaVariable boundSchemaVariable =
        	    (SchemaVariable) boundVar;
        	if (svInst.isInstantiated(boundSchemaVariable)) {
        	    boundVar = ((QuantifiableVariable) ((Term) svInst
        		    .getInstantiation(boundSchemaVariable))
        		    .op());
        	} else {
        	    // this case may happen for PO generation of
        	    // taclets
        	    boundVar = (QuantifiableVariable)boundSchemaVariable;
        	}
        	varsChanged = true;
            }
            newVars[j] = boundVar;
        }

        return  varsChanged
        	? new ImmutableArray<QuantifiableVariable>(newVars)
                : vBoundVars;
    }
    
    /**
     * performs the syntactic replacement of schemavariables with their
     * instantiations
     */
    public void visit(Term visited) {
        // Sort equality has to be ensured before calling this method
        final Operator visitedOp = visited.op();
        if (visitedOp instanceof SchemaVariable
                && visitedOp.arity() == 0
                && svInst.isInstantiated((SchemaVariable) visitedOp)
                && (!(visitedOp instanceof ProgramSV && ((ProgramSV) visitedOp)
                        .isListSV()))) {
            Term newTerm = toTerm(svInst.getInstantiation((SchemaVariable) visitedOp));
            pushNew(TermBuilder.DF.label(
                    newTerm, instantiateLabels(visited, newTerm.op(), newTerm.subs(),
                                               newTerm.boundVars(), newTerm.javaBlock(), "visit")));
        } else if ((visitedOp instanceof Metavariable)
                && metavariableInst.getInstantiation((Metavariable) visitedOp)
                        .op() != visitedOp) {
            pushNew(metavariableInst.getInstantiation((Metavariable) visitedOp));
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
            final ImmutableArray<QuantifiableVariable> boundVars = instantiateBoundVariables(visited);

            // instantiate annotations
            
            // instantiate sub terms
            Term[] neededsubs = neededSubs(newOp.arity());
            if (visitedOp instanceof ElementaryUpdate
                    && elementaryUpdateLhs != null) {
                assert neededsubs.length == 1;
                Term newTerm = TermBuilder.DF.elementary(services,
                        elementaryUpdateLhs, neededsubs[0]);
                ImmutableArray<TermLabel> labels =
                        instantiateLabels(visited, newTerm.op(), newTerm.subs(), newTerm.boundVars(),
                                          newTerm.javaBlock(), "elementary");
                if (labels.size() != 0) {
                    newTerm = TermBuilder.DF.label(newTerm, labels);
                }
                pushNew(newTerm);
            } else if (boundVars != visited.boundVars() || jblockChanged
                    || operatorInst
                    || (!subStack.empty() && subStack.peek() == newMarker)) {
                ImmutableArray<TermLabel> labels =
                        instantiateLabels(visited, newOp, new ImmutableArray<Term>(neededsubs),
                                          boundVars, jb, "boundVars");
               Term newTerm = tf.createTerm(newOp, neededsubs, boundVars, jb, labels);
                pushNew(resolveSubst(newTerm));
            } else {
                Term t;
                ImmutableArray<TermLabel> labels =
                        instantiateLabels(visited, visited.op(), visited.subs(), visited.boundVars(),
                                          visited.javaBlock(), "else");
                if (!visited.hasLabels() && labels != null && labels.isEmpty()) {
                   t = visited;
                }
                else {
                   t = TermFactory.DEFAULT.createTerm(visited.op(), visited.subs(),
                                                      visited.boundVars(),
                                                      visited.javaBlock(), labels);
                }
                t = resolveSubst(t);
                if (t == visited)
                    subStack.push(t);
                else
                    pushNew(t);
            }
        }
    }

    private ImmutableArray<TermLabel> instantiateLabels(Term tacletTerm,
                                                        Operator newTermOp,
                                                        ImmutableArray<Term> newTermSubs,
                                                        ImmutableArray<QuantifiableVariable>
                                                                        newTermBoundVars,
                                                        JavaBlock newTermJavaBlock,
                                                        Object hint) {
       return TermLabelManager.instantiateLabels(services, applicationPosInOccurrence, rule, null,
                                                 hint, tacletTerm, newTermOp, newTermSubs,
                                                 newTermBoundVars, newTermJavaBlock);
    }

    private Operator handleSortDependingSymbol (SortDependingFunction depOp) {
        final Sort depSort = depOp.getSortDependingOn ();

        final Sort realDepSort =
            svInst.getGenericSortInstantiations ()
                                       .getRealSort ( depSort, getServices() );


        final Operator res = depOp.getInstanceFor ( realDepSort, services );
        Debug.assertFalse ( res == null,
                            "Did not find instance of symbol "
                            + depOp + " for sort " + realDepSort );
        return res;
    }

    private Term resolveSubst(Term t) {
	if (resolveSubsts && t.op() instanceof SubstOp)
	    return ((SubstOp)t.op ()).apply ( t );
	return t;
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
    public ImmutableMap<SchemaVariable,Term> getNewInstantiations () {
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
	if (subtreeRoot.op() instanceof TermTransformer) {
	    TermTransformer mop = (TermTransformer) subtreeRoot.op();
	    Term newTerm = mop.transform((Term)subStack.pop(),svInst, getServices());
	    pushNew(TermBuilder.DF.label(newTerm,
	                                 instantiateLabels(subtreeRoot, newTerm.op(),
	                                                   newTerm.subs(), newTerm.boundVars(),
	                                                   newTerm.javaBlock(), "subtreeLeft")));
	} 
   }
}
