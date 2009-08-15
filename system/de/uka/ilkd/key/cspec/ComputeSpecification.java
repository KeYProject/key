// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.cspec;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.util.Debug;

/**
 * This class is the <em>central</em> facade for computing the specification of a
 * program. It contains algorithms for and controls the computation of specifications.
 * <h3>Internals</h3>
 * Usually, specification construction process is started by invoking {@link
 * de.uka.ilkd.key.proof.init.SpecExtPO} to construct the
 * specification computation proof obligation. Finally, the whole
 * system relies on the functionality of this class to
 * {@link #createSpecificationComputationTerm(JavaBlock,Namespace) construct the
 * specification computation obligation} initially, and
 * {@link #computeSpecification(Proof) excerpt the
 * specification} at the end of the proof attempt.
 *
 * @author Andr&eacute; Platzer
 * @version 0.1, 2003-01-28
 * @version-revision $Revision: 1.16.3.1.2.1.3.1.1.3.2.2 $, $Date: Mon, 22 Jan 2007 15:50:58 +0100 $
 * @see de.uka.ilkd.key.gui.ComputeSpecificationView
 */
public class ComputeSpecification {
    /**
     * Only remember prestate, implicitly.
     * Thus use proof obligations like &lt;program&gt; (xpost=x).
     */
    public static final int PRESTATE_REMEMBER_IMPLICIT = 0;
    /**
     * Use explicit prestate remembrance equations.
     * Thus use proof obligations like x=xpre &larr; &lt;program&gt; (xpost=x).
     */
    public static final int PRESTATE_REMEMBER_EQUATIONS = 1;
    /**
     * Use updates for prestate remembrance.
     * Thus use proof obligations like {x:=xpre} &lt;program&gt; (xpost=x).
     */
    public static final int PRESTATE_REMEMBER_UPDATES = 2;
    /**
     * Which variant to use for remembering the prestate of the program
     * invocation.
     * @see #PRESTATE_REMEMBER_EQUATIONS
     * @see #PRESTATE_REMEMBER_UPDATES
     * @see #PRESTATE_REMEMBER_IMPLICIT
     */
    private static int prestateRemember = PRESTATE_REMEMBER_UPDATES;
    /**
     * set prestate remember kind by property
     */
    static {
	String property = ComputeSpecification.class.getName() + ".prestateRemember";
	try {
	    String desc = System.getProperty(property, prestateRemember + "");
	    try {
		setPrestateRemember(java.lang.Integer.parseInt(desc));
	    } catch (NumberFormatException nonumber) {
		Debug.out("invalid property setting" , property, desc);
	    } 
	}
	catch (SecurityException nevertheless) {
	    // especially catch SecurityExceptions if we were not allowed to read properties
	    Debug.out("Exception thrown by class ComputeSpecification at getProperty()");
	}
	catch (Exception nevertheless) {
	    Debug.out("use default property setting for " , property, nevertheless);
	} 
	Debug.out("property setting ", property, new Integer(prestateRemember));
    }

    /**
     * Use explicit poststate remember equations
     * (x1=x1@post & ...& xn=xn@post).
     * Requires knowledge of the modifies list.
     */
    public static final int POSTSTATE_REMEMBER_EQUATIONS = 1;
    /**
     * Use state change accumulatorr ^true alias scripted C for remembering
     * the poststate.
     * Does not require knowledge of the modifies list.
     * <code>false</code> for explicit poststate remember terms
     * (x1=x1@post & ...& xn=xn@post) which requires knowledge of the modifies list.
     */
    public static final int POSTSTATE_REMEMBER_STATE_CHANGE_ACCUMULATION = 2;

    /**
     * Which variant to use for remembering the poststate of the program
     * invocation.
     * @see #POSTSTATE_REMEMBER_EQUATIONS
     * @see #POSTSTATE_REMEMBER_STATE_CHANGE_ACCUMULATION
     */
    private static int poststateRemember = POSTSTATE_REMEMBER_STATE_CHANGE_ACCUMULATION;

    private static final TermFactory termFactory = TermFactory.DEFAULT;
    
    /**
     * Which variant to use for remembering the prestate of the program
     * invocation.
     * @see #PRESTATE_REMEMBER_EQUATIONS
     * @see #PRESTATE_REMEMBER_UPDATES
     * @see #PRESTATE_REMEMBER_IMPLICIT
     */
    public static final void setPrestateRemember(int prestateRememberMode) {
	if (PRESTATE_REMEMBER_IMPLICIT <= prestateRememberMode
	    && prestateRememberMode <= PRESTATE_REMEMBER_UPDATES) {
	    prestateRemember = prestateRememberMode;
	} else {
	    throw new IllegalArgumentException("illegal prestate remember mode: " + prestateRememberMode);
	}
    }
    public static final int getPrestateRemember() {
	return prestateRemember;
    }

    /**
     * Which variant to use for remembering the poststate of the program
     * invocation.
     * @see #POSTSTATE_REMEMBER_EQUATIONS
     * @see #POSTSTATE_REMEMBER_STATE_CHANGE_ACCUMULATION
     */
    public static final void setPoststateRemember(int poststateRememberMode) {
	if (POSTSTATE_REMEMBER_EQUATIONS <= poststateRememberMode
	    && poststateRememberMode <= POSTSTATE_REMEMBER_STATE_CHANGE_ACCUMULATION) {
	    poststateRemember = poststateRememberMode;
	} else {
	    throw new IllegalArgumentException("illegal poststate remember mode: " + poststateRememberMode);
	}
    }
    public static final int getPoststateRemember() {
	return poststateRemember;
    }
    
    /**
     * This uninterpreted function is used to accumulate updates instead of throwing
     * the state change information away. 
     */
    public static final Function ACCUMULATOR = 
        new NonRigidFunction(new Name("acc"), Sort.FORMULA, new Sort[0]);
    
    public ComputeSpecification() {
	
    }

    // term constructor method
    
    /**
     * Creates the term to analyse for computing the specification of
     * a program. Feeding this term into a proof passed to {@link
     * #computeSpecification(KeYMediator)}, or {@link
     * #computeSpecification(Proof)} will result in the specification.
     * @param program the program of which to compute a specification.
     * @param programVariables the variables that program possibly modifies.
     * @return the term required for constructing the specification.
     */
    public static Term createSpecificationComputationTerm(JavaBlock program,
						          Namespace programVariables) {
	// Construct a proof obligation of a form like
	// x = xpre & y = ypre -> <{program}> (xpost = x & ypost = y)
	Term precondition = termFactory.createJunctorTerm(Op.TRUE);
	Term postcondition = termFactory.createJunctorTerm(Op.TRUE);
	       
        ImmutableList<Term> prestateLocations = ImmutableSLList.<Term>nil();
	ImmutableList<Term> prestateValues = ImmutableSLList.<Term>nil(); 
	for (Iterator<Named> i = programVariables.elements().iterator();
	     i.hasNext();
	     ) {
	    final ProgramVariable v = (ProgramVariable) i.next();
	    final Term v_term = termFactory
		.createVariableTerm(v);
	    Debug.out("program variable ", v, v.getKeYJavaType());
	    if ("self".equals(v.name().toString())) {
		// @xxx currently ignore modifications of object state, so no need to remember
	    } else {
		final Term vpre = termFactory
		    .createVariableTerm(new LocationVariable(new ProgramElementName(v.name() + "pre"), v.getKeYJavaType()));
		final Term vpost = termFactory
		    .createVariableTerm(new LocationVariable(new ProgramElementName(v.name() + "post"), v.getKeYJavaType()));

		if ("result".equals(v.name().toString())) {
		    // ignore result at prestate
		} else {
		    // prestate = prestate union {v:=vpre}
		    prestateLocations = prestateLocations.append(v_term);
		    prestateValues = prestateValues.append(vpre);
		    // remember prestate of v
		    precondition = termFactory
			.createJunctorTermAndSimplify(Op.AND,
						      precondition,
						      termFactory
						      .createEqualityTerm(
									  v.sort().getEqualitySymbol(),
									  termFactory
									  .createVariableTerm(v),
									  vpre
									  )
						      );
		}

		// construct poststate of v
		postcondition = termFactory
		    .createJunctorTermAndSimplify(Op.AND,
				       postcondition,
				       termFactory
				       .createEqualityTerm(
							   v.sort().getEqualitySymbol(),
							   vpost,
							   termFactory
							   .createVariableTerm(v)
							   )
				       );
	    }
	}

	switch (getPoststateRemember()) {
	case POSTSTATE_REMEMBER_EQUATIONS:
	    /* already assigned postcondition above */
	    break;
	case POSTSTATE_REMEMBER_STATE_CHANGE_ACCUMULATION:
	    /* alter already assigned postcondition */
	    postcondition = TermBuilder.DF.func(ACCUMULATOR);
	    break;
	default:
	    throw new IllegalStateException("illegal kind of poststate remembering terms: " + getPoststateRemember());
	}

	final Term diamondTerm = termFactory.createDiamondTerm(program, postcondition);
	switch (getPrestateRemember()) {
	case PRESTATE_REMEMBER_IMPLICIT:
	    return diamondTerm;

	case PRESTATE_REMEMBER_UPDATES:
	    return prestateLocations.size() == 0
		//@internal createUpdateTerm does not work for empty update lists
		? diamondTerm
		// updates prestate (diamondTerm)
		: termFactory.createUpdateTerm(prestateLocations.toArray(new Term[prestateLocations.size()]), 
			prestateValues.toArray(new Term[prestateValues.size()]), diamondTerm);
	    
	case PRESTATE_REMEMBER_EQUATIONS:
	    return termFactory.createJunctorTermAndSimplify(Op.IMP, precondition, diamondTerm);
	default:
	    throw new IllegalStateException("illegal kind of prestate remembering terms: " + getPrestateRemember());
	}
    }

    

    // specification computation

    /**
     * Extracts the specification of a program from a failed attempt
     * to prove its correctness.
     * Will continue the proof automatically as far as possible.
     * @param mediatorContainingProof The mediator containing
     *  the specification computation proof as selected proof.
     *  Its proof obligation usually stems from
     * {@link #createSpecificationComputationTerm(JavaBlock,Namespace)}.
     */
    public Term computeSpecification(KeYMediator mediatorContainingProof) {
	final KeYMediator mediator = mediatorContainingProof;
	//@internal we could also use a "Future" as synchronization means. Perhaps also a Z modulo 2=1 semaphore.
	final PersistentCondition proofStopped = new PersistentCondition();
	mediator.addAutoModeListener(new AutoModeListener() {

		public void autoModeStarted(ProofEvent param1)
		{
		}

		public void autoModeStopped(ProofEvent param1)
		{
		    Debug.out("proof finished signalled");
		    proofStopped.signal();
		}
	    });

	mediator.getInteractiveProver().startAutoMode();

	try {
	    // let's wait until the prover finishes
	    proofStopped.waitFor();
	    Debug.out("proof finished heard");

	    return computeSpecification(mediator.getSelectedProof());
	}
	catch (InterruptedException interrupt) {
	    Thread.currentThread().interrupt();
	    throw new Error("cannot compute specification since construction process has been interrupted");
	}
    }

    /**
     * Extracts the specification of a program from a failed attempt
     * to prove its correctness.
     * @preconditions proof has no more applicable inference rules.
     * @param proof The specification computation proof driven as far as possible.
     *  Its proof obligation usually stems from
     * {@link #createSpecificationComputationTerm(JavaBlock,Namespace)}.
     */
    public Term computeSpecification(Proof proof) {
	Debug.out("Compute specification:\n");
	List caseSpecs = new LinkedList();
	for (Iterator<Goal> i = proof.openGoals().iterator(); i.hasNext(); ) {
	    Sequent open = i.next().sequent();
	    Term caseSpec = computeSpecification(open);
	    Debug.out("Goal Case" , caseSpec);
	    caseSpecs.add(caseSpec);
	}
	return createJunctorTermNAry(termFactory.createJunctorTerm(Op.TRUE),
				     Op.AND,
				     caseSpecs.iterator()
				     );
    }

    /**
     * Constructs the specification resulting of a single open-goal
     * sequent.
     * @internal to be precise, we would have to distinguish pure
     * first-order open-goals, from open-goals still containing
     * dynamic logic.
     */
    private Term computeSpecification(Sequent seq) {
	Semisequent ante = seq.antecedent();
	Debug.out("\nCase ");
	Term ante2 = createJunctorTermNAryCF(termFactory.createJunctorTerm(Op.TRUE),
					   Op.AND,
					   ante.iterator()
					   );
	Debug.out("", ante2);
	Debug.out(" => ");
	Semisequent succ = seq.succedent();
	Term succ2 = createJunctorTermNAryCF(termFactory.createJunctorTerm(Op.FALSE),
					   Op.OR,
					   succ.iterator()
					   );
	Debug.out("", succ2);

	return termFactory.createJunctorTermAndSimplify(Op.IMP, ante2, succ2);
    }

    
    // trivial helper methods

    /**
     * Explicit n-ary-fied version of {@link
     * de.uka.ilkd.key.logic.TermFactory#createJunctorTerm(Junctor,Term[])}.
     * see orbital.logic.functor.Functionals#foldRight
     * @internal almost identical to @see #createJunctorTermNAry(Term,Junctor,IteratorOfTerm)
     */
    private static final Term createJunctorTermNAryCF(Term c, Junctor op, Iterator<ConstrainedFormula> i) {
	Term construct = c;
	while (i.hasNext()) {
	    ConstrainedFormula f = i.next();
	    Term t = f.formula();
	    //	   ignore tautological constraints, since they do not contribute to the specification
            // but report others
            if (!f.constraint().isBottom())
		throw new IllegalArgumentException("there is a non-tautological constraint on " + f + ". lower constraints, first");
	    construct = termFactory.createJunctorTermAndSimplify(op, construct, t);
	}
	return construct;
    }
    /**
     * Explicit n-ary-fied version of {@link
     * de.uka.ilkd.key.logic.TermFactory#createJunctorTerm(Junctor,Term[])}.
     * see orbital.logic.functor.Functionals#foldRight
     */
    private static final Term createJunctorTermNAry(Term c, Junctor op, Iterator<Term> i) {
	Term construct = c;
	while (i.hasNext()) {
	    construct = termFactory.createJunctorTermAndSimplify(op, construct, i.next());
	}
	return construct;
    }
}// ComputeSpecification


