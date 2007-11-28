// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import java.util.HashSet;
import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.ProgramSkolemInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;



public class ProgramVariableSkolemBuilder
    extends AbstractSkolemBuilder {

    private final RawProgramVariablePrefixes rpvp;
    private ListOfSkolemSet results = SLListOfSkolemSet.EMPTY_LIST;

    public ProgramVariableSkolemBuilder ( SkolemSet                  p_oriSkolemSet,
					  RawProgramVariablePrefixes p_rpvp,
					  Services                   p_services ) {
	super ( p_oriSkolemSet, p_services );
	rpvp = p_rpvp;
    }
    
    public IteratorOfSkolemSet build () {
	build ( 0,
		new HashSet (),
		getOriginalSkolemSet ().getInstantiations () );
	return results.iterator();
    }

    private void addResult(SkolemSet p) {
        results = results.prepend(p);
    }

    private void build ( int              p_variableNumber,
			 HashSet          p_usedVariables,
			 SVInstantiations p_currentSVI ) {
	if ( p_variableNumber == getSVPartitioning().size () ) {
	    addResult ( getOriginalSkolemSet ()
	                .addVariables ( toNamespace(p_usedVariables) )
	                .add ( p_currentSVI ) );
	    return;
	}
	
	if ( getSVPartitioning().isExpressionSV(p_variableNumber) ) {
	    // Expression schema variables are instantiated by a
	    // dedicated builder
	    build ( p_variableNumber + 1, p_usedVariables, p_currentSVI );
	    return;
	}
	
	PVCandidate[] pvs = createPVCandidates ( p_variableNumber,
						 p_currentSVI,
						 p_usedVariables );

	for ( int i = 0; i != pvs.length; ++i ) {
	    p_usedVariables.add    ( pvs[i].pv );
	    
	    build ( p_variableNumber + 1,
		    p_usedVariables,
		    pvs[i].svi );
		
	    p_usedVariables.remove ( pvs[i].pv );
	}
    }

    private Namespace toNamespace(HashSet p_usedVariables) {
        final Namespace vars = new Namespace ();
        
        final Iterator  it   = p_usedVariables.iterator ();
        while ( it.hasNext () )
            vars.add ( (Named)it.next () );

        return vars;
    }

    private PVCandidate[]
	createPVCandidates ( int              p_variableNumber,
			     SVInstantiations p_currentSVI,
			     HashSet          p_usedVars ) {
	final ExtList              res  = new ExtList ();
	final ListOfSchemaVariable svs  =
	    getSVPartitioning().getPartition ( p_variableNumber );
	final KeYJavaType          type = getPartitionType(p_variableNumber);

	Debug.assertFalse ( type == null,
	                    "Type of schema variables " + svs +
                            " should be determined at this point" );

	if ( getSVPartitioning().isNative(p_variableNumber) )
	    createNativePVCandidates ( svs, type, p_currentSVI,
				       p_usedVars, res );
	else
	    createNewPVCandidate     ( svs, type, p_currentSVI, res,
				       ProgramSkolemInstantiation
				       .NEW_BOUND_VARIABLE );

	return (PVCandidate[])res.collect ( PVCandidate.class );
    }

    
    /**
     * Instantiate the given set of schema variables with all existing
     * program variables of type <code>p_type</code>, and add the
     * resulting entries to the object <code>p_currentSVI</code>. The
     * program variable as well as the new
     * <code>SVInstantiations</code> object is added to
     * <code>p_res</code> within an <code>PVCandidate</code> object.
     * @param p_type the type the new variable is to be given
     */
    private void createNativePVCandidates ( ListOfSchemaVariable p_svs,
					    KeYJavaType          p_type,
					    SVInstantiations     p_currentSVI,
					    HashSet              p_usedVars,
					    ExtList              p_res ) {
	final IteratorOfIProgramVariable nativeIt =
	    rpvp.getFreeProgramVariables ().iterator ();

	while ( nativeIt.hasNext () ) {
	    final IProgramVariable pv = nativeIt.next ();

	    if ( p_usedVars.contains ( pv ) || pv.getKeYJavaType() != p_type )
		continue;

	    final PVCandidate pvc =
	        performInstantiation ( p_currentSVI,
	                               p_svs, 
				       pv,
				       ProgramSkolemInstantiation
				       .OCCURRING_VARIABLE );

	    p_res.add ( pvc );
	}
    }


    /**
     * Instantiate the given set of schema variables with a new
     * program variable, and add the resulting entries to the object
     * <code>p_currentSVI</code>. The created program variable as well
     * as the new <code>SVInstantiations</code> object is added to
     * <code>p_res</code> within an <code>PVCandidate</code> object.
     * @param p_type the type the new variable is to be given
     */
    private void createNewPVCandidate ( ListOfSchemaVariable p_svs,
					KeYJavaType          p_type,
					SVInstantiations     p_currentSVI,
					ExtList              p_res,
					int                  p_instantiationType ) {
	final String baseName = "" + p_svs.head ().name () + "_" +
	                        p_type.getJavaType ().getFullName ();

        final IProgramVariable pv  =
	    new LocationVariable ( createUniquePEName(baseName), p_type );

	final PVCandidate      pvc = performInstantiation ( p_currentSVI,
	                                                    p_svs,
				                            pv,
							    p_instantiationType );

	p_res.add ( pvc );
    }


    private PVCandidate
	performInstantiation ( SVInstantiations     p_currentSVI,
			       ListOfSchemaVariable p_svs,
			       IProgramVariable     p_pv,
			       int                  p_instantiationType ) {

	SVInstantiations svi =
	    StaticCheckerSVI.addInstantiation ( p_currentSVI, p_svs, p_pv,
						p_instantiationType );

	Debug.assertFalse ( svi == null,
			    "Instantiation of " + p_svs +
			    " with program variable " + p_pv + " failed" );

	return new PVCandidate ( p_pv, svi );
    }


    private static class PVCandidate {
	public final IProgramVariable pv;
	public final SVInstantiations svi;

	public PVCandidate ( IProgramVariable p_pv,
			     SVInstantiations p_svi ) {
	    pv   = p_pv;
	    svi  = p_svi;
	}
    }
}
