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


package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/** 
 * A no position taclet application has no position information yet. This can
 * have different reasons: <ul>
 *  <li> the taclet application belongs to a no find taclet, this means it is
 * attached to a sequent and not to a formula or term. </li>
 *  <li> the taclet application has not been matched against a term or formula,
 * but may already contain instantiation information for some of its
 * schemavariables. This is the case, if the taclet of this application object
 * has been inserted by an addrule part of another taclet. For this reason 
 * the {@link de.uka.ilkd.key.proof.TacletIndex} manages no position taclet
 * application objects instead of the taclets itself. 
 * </li> </ul>
 * 
 */
public class NoPosTacletApp extends TacletApp {

    /** creates a NoPosTacletApp for the given taclet and no instantiation
     * information and CHECKS variable conditions as well as it resolves
     * collisions
     * @param taclet the Taclet 
     */
    public static NoPosTacletApp createNoPosTacletApp(Taclet taclet) {
	return new UninstantiatedNoPosTacletApp(taclet);
    }

    /** creates a NoPosTacletApp for the given taclet with some known
     * instantiations and CHECKS variable conditions as well as it
     * resolves collisions
     * The ifInstantiations parameter is not
     * matched against the if sequence, but only stored. For matching
     * use the method "setIfFormulaInstantiations".
     * @param taclet the Taclet 
     * @param instantiations the SVInstantiations
     */
    public static NoPosTacletApp
	createNoPosTacletApp(Taclet           taclet, 
			     SVInstantiations instantiations,
			     Services         services) {
	return createNoPosTacletApp ( taclet,
				      instantiations,
				      null,
				       services);
    }

    public static NoPosTacletApp
	createNoPosTacletApp(Taclet                       taclet, 
			     SVInstantiations             instantiations,
			     ImmutableList<IfFormulaInstantiation> ifInstantiations,
			     Services                     services) {
	Debug.assertTrue ( ifInstsCorrectSize ( taclet, ifInstantiations ),
			   "If instantiations list has wrong size" );

	SVInstantiations inst = resolveCollisionVarSV(taclet, 
						      instantiations,
						      services);
	if (checkVarCondNotFreeIn(taclet, inst)) {
	    return new NoPosTacletApp(taclet,
				      inst,
				      ifInstantiations);
	} 
	return null;
    }
 
    public static NoPosTacletApp createNoPosTacletApp(Taclet             taclet,
						      MatchConditions    matchCond,
						      Services           services) {
	return createNoPosTacletApp ( taclet,
				      matchCond.getInstantiations   (),
				      null,
				      services);
    }
   
    /**
     * Create TacletApp with immutable "instantiations", i.e. this
     * instantiations must not be modified later (e.g. by
     * "addInstantiation"). However, this information is currently
     * only used to decide about introduction of
     * metavariables. Immutable instantiations are important for the
     * "addrules" part of taclets.
     */
    public static NoPosTacletApp
	createFixedNoPosTacletApp( Taclet             taclet,
				   SVInstantiations   instantiations,
				   Services           services) {
	NoPosTacletApp res = createNoPosTacletApp ( taclet,
						    instantiations,
						    null,
						    services);
	// Make the given SVs fixed
	if ( res != null ) {
	    final Iterator<SchemaVariable> it = instantiations.svIterator ();
	    while ( it.hasNext () ) {
		res.fixedVars = res.fixedVars.add ( it.next () );
            }
            res.updateContextFixed = true;
        }
	return res;
    }
   
    
    /** creates a NoPosTacletApp for the given taclet and no instantiation
     * information
     * @param taclet the Taclet 
     */
    protected NoPosTacletApp(Taclet taclet) {
	super(taclet);
    }

    /** creates a NoPosTacletApp for the given taclet with some known instantiations
     * @param taclet the Taclet 
     * @param instantiations the SVInstantiations
     */
    private NoPosTacletApp(Taclet                       taclet,
			   SVInstantiations             instantiations,
			   ImmutableList<IfFormulaInstantiation> ifInstantiations) {
	super(taclet,
	      instantiations,
	      ifInstantiations);
    }


    /** checks if the variable conditions of type 'x not free in y' are
     * hold by the found instantiations. The variable conditions is used
     * implicit in the prefix. (Used to calculate the prefix)
     * @param taclet the Taclet that is tried to be instantiated. A match for the
     * find (or/and if) has been found.
     * @param instantiations the SVInstantiations so that the find(if) matches
     * @return true iff all variable conditions x not free in y are hold
     */
    protected static boolean checkVarCondNotFreeIn(Taclet taclet,
					 SVInstantiations instantiations) {
	final Iterator<SchemaVariable> it = instantiations.svIterator();
	while ( it.hasNext () ) {
            final SchemaVariable sv = it.next ();

	    if ( sv instanceof ModalOperatorSV
	         || sv instanceof ProgramSV
                 || sv instanceof VariableSV
                 || sv instanceof SkolemTermSV)
                continue;

	    final TacletPrefix prefix = taclet.getPrefix ( sv );
            if ( prefix.context () ) continue;
        
	    final ImmutableSet<QuantifiableVariable> boundVarSet =
	        boundAtOccurrenceSet ( prefix, instantiations );
	    final Term inst = (Term)instantiations.getInstantiation ( sv );
	    if ( !inst.freeVars ().subset ( boundVarSet ) ) return false;
	}
    
	return true;
    }


    /** adds a new instantiation to this TacletApp 
     * @param sv the SchemaVariable to be instantiated
     * @param term the Term the SchemaVariable is instantiated with
     * @return the new TacletApp
     */
    public TacletApp addInstantiation(SchemaVariable sv, 
	    			      Term term,
				      boolean interesting,
				      Services services) {
	if (interesting)
	    return createNoPosTacletApp(taclet(), 
					instantiations()
					.addInteresting(sv, term, services),
					ifFormulaInstantiations (),
					services);
	else
	    return createNoPosTacletApp(taclet(), 
					instantiations().add(sv, term, services),
					ifFormulaInstantiations (),
					services);
    }


    
    public TacletApp addInstantiation(SchemaVariable sv, 
	    			      Object[] list,
	    			      boolean interesting,
	    			      Services services) {
	if (interesting) {
	    return createNoPosTacletApp(taclet(), 
		    			instantiations().addInterestingList(sv, list, services), 
		    			ifFormulaInstantiations(),
		    			services);
	} else {
	    return createNoPosTacletApp(taclet(), 
		    			instantiations().addList(sv, list, services), 
		    			ifFormulaInstantiations(), 
		    			services);
	}
    }
    
    

    /**
     * adds a new instantiation to this TacletApp
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param pe
     *            the ProgramElement the SV is instantiated with
     * @return the new TacletApp
     */
    public TacletApp addInstantiation(SchemaVariable sv, 
	    			      ProgramElement pe,
				      boolean interesting,
				      Services services) {
	if (interesting) {
	    return createNoPosTacletApp(taclet(), 
					instantiations()
					.addInteresting(sv, pe, services),
					ifFormulaInstantiations (),
					services);
	} else { 
	    return createNoPosTacletApp(taclet(), 
					instantiations().add(sv, pe, services),
					ifFormulaInstantiations (),
					services);
	}
    }


    /**
     * creates a new Taclet application containing all the
     * instantiations given 
     * by the SVInstantiations and hold the old ones
     * @param svi the SVInstantiations whose entries are the needed
     * instantiations 
     * @return the new Taclet application
     */
    public TacletApp addInstantiation(SVInstantiations svi,
	    			      Services services) {
	return new NoPosTacletApp(taclet(),
				  svi.union(instantiations(), services),
				  ifFormulaInstantiations ());
    }


    /**
     * creates a new Taclet application containing all the
     * instantiations given 
     * by the SVInstantiations and forget the ones in this TacletApp
     * @param svi the SVInstantiations whose entries are the needed
     * instantiations 
     * @return the new Taclet application
     */
    @Override
    protected TacletApp setInstantiation(SVInstantiations svi,
	    				 Services services) {
	return new NoPosTacletApp(taclet(), svi,
				  ifFormulaInstantiations ());
    }


    /**
     * creates a new Taclet application containing all the
     * instantiations, constraints and new metavariables given 
     * by the mc object and forget the old ones
     */
    public TacletApp setMatchConditions(MatchConditions mc,
	    				Services services) {
	return createNoPosTacletApp( taclet(),
				     mc.getInstantiations   (),
				     ifFormulaInstantiations (),
				     services);
    }


    /**
     * creates a new Taclet application containing all the
     * instantiations, constraints, new metavariables and if formula
     * instantiations given and forget the old ones
     */
    protected TacletApp setAllInstantiations ( MatchConditions              mc,
					       ImmutableList<IfFormulaInstantiation> ifInstantiations,
					       Services                     services) {
	return createNoPosTacletApp( taclet(),
				     mc.getInstantiations   (),
				     ifInstantiations,
				     services);
    }


    /** returns true iff all necessary informations are collected, so
     * that the Taclet can be applied.
     * @return true iff all necessary informations are collected, so
     * that the Taclet can be applied.
     */
    public boolean complete() {
	return ( uninstantiatedVars().isEmpty()
		 && taclet() instanceof NoFindTaclet
		 && ifInstsComplete () );

    }

    protected ImmutableSet<QuantifiableVariable> contextVars(SchemaVariable sv) {
	return DefaultImmutableSet.<QuantifiableVariable>nil();
    }


    /**
     * returns the PositionInOccurrence (representing a SequentFormula and
     * a position in the corresponding formula)
     * @return the PosInOccurrence
     */
    public PosInOccurrence posInOccurrence() {
	return null;
    }

    /**
     * PRECONDITION: ifFormulaInstantiations () == null &&
     *               ( pos == null || termConstraint.isSatisfiable () )
     * @return TacletApp with the resulting instantiations or null
     */
    public NoPosTacletApp matchFind(PosInOccurrence pos,
				    Services        services) {
        NoPosTacletApp result = matchFind(pos, services, null);
	return result;
    }


    /* This is a short-circuit version of matchFind(). It helps eliminate
       numerous calls to the expensive pos.subTerm() while matching during
       a recursive descent in a term (where the current subterm is known 
       anyway).
     */
    public NoPosTacletApp matchFind(PosInOccurrence pos,
				    Services        services,
				    Term t) {
        if ((t==null) && (pos!=null)) t = pos.subTerm ();

        MatchConditions mc = setupMatchConditions(pos, services);
        
        if ( mc == null )
            return null;
        
        MatchConditions res = null;
	if (taclet() instanceof FindTaclet) {	   
		res = ((FindTaclet)taclet())
		    .matchFind ( t,
				 mc,
				 services );
		// the following check will partly be repeated within the
		// constructor; this could be optimised
		if ( res == null ||
		     !checkVarCondNotFreeIn(taclet(), 
                             res.getInstantiations(), pos) )
		    return null;
	} else {
	    res = mc;
	}
        
        return evalCheckRes(res, services);
    }

    private NoPosTacletApp evalCheckRes(MatchConditions res, 
	    			        Services services) {
	if ( res == null )
	    return null;

	if ( updateContextFixed &&
	     !updateContextCompatible ( res ) ) {
           /* Debug.out("NoPosTacletApp: Incompatible context", instantiations.getUpdateContext (),
                      res.matchConditions().getInstantiations().getUpdateContext());*/
            return null;
        }

	return (NoPosTacletApp)setMatchConditions ( res, services );
    }

    
    protected MatchConditions setupMatchConditions(PosInOccurrence pos,
		  				   TermServices services) {
	SVInstantiations svInst = taclet() instanceof NoFindTaclet ? 
                instantiations   () : instantiations   ().clearUpdateContext ();
        
                MatchConditions mc  =
	    new MatchConditions ( svInst,
				  RenameTable.EMPTY_TABLE);
        
	if ( taclet() instanceof RewriteTaclet ) {
	    mc = ((RewriteTaclet)taclet ()).checkPrefix ( pos,
								mc );
	    if (mc == null) {
                Debug.out("NoPosTacletApp: Update prefix check failed.");
            }
        }
        
	return mc;
    }


    private boolean updateContextCompatible ( MatchConditions p_mc ) {
	return 
	    instantiations.getUpdateContext ()
	    .equals ( p_mc.getInstantiations ().getUpdateContext () );
    }

    
    @Override
    public boolean equals(Object o) {
    	if (o == this) return true;
    	if (!(o instanceof NoPosTacletApp)) return false;
    	return super.equals(o);
    }
    
    
    @Override
    public int hashCode() {
    	return super.hashCode();
    }    
}
