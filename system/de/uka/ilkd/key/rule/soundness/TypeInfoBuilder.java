// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.ProgramSkolemInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.ExtList;


/**
 * Choose types for the untyped schema variables for PV and
 * expressions
 */
public class TypeInfoBuilder extends AbstractSkolemBuilder {

    private final RawProgramVariablePrefixes rpvp;
    private ImmutableList<SkolemSet> results = ImmutableSLList.<SkolemSet>nil();

    public TypeInfoBuilder ( SkolemSet                  p_oriSkolemSet,
			     RawProgramVariablePrefixes p_rpvp,
			     Services                   p_services ) {
        super(p_oriSkolemSet, p_services);
	rpvp = p_rpvp;
    }

    public Iterator<SkolemSet> build() {
	build ( 0,
		getOriginalSkolemSet ().getInstantiations (),
		getOriginalSkolemSet ().getSVTypeInfos () );

        return handleSubsumption ( results.iterator () );
    }

    private void addResult(SkolemSet p) {
        results = results.prepend(p);
    }

    private void build ( int              p_variableNumber,
			 SVInstantiations p_currentSVI,
			 SVTypeInfos      p_currentSVTI ) {
	if ( p_variableNumber == getSVPartitioning().size () ) {
	    addResult( getOriginalSkolemSet ()
	               .setSVTypeInfos ( p_currentSVTI ) );
	    return;
	}
	
	PVCandidate[] pvs = createPVCandidates ( p_variableNumber,
				                 p_currentSVI,
				                 p_currentSVTI );

	int i;
	for ( i = 0; i != pvs.length; ++i ) {
	    build ( p_variableNumber + 1,
		    pvs[i].svi,
		    pvs[i].svti );
	}
    }

    private PVCandidate[]
	createPVCandidates ( int              p_variableNumber,
			     SVInstantiations p_currentSVI,
			     SVTypeInfos      p_currentSVTI ) {
	final ExtList              res  = new ExtList ();
	final ImmutableList<SchemaVariable> svs  =
	    getSVPartitioning ().getPartition ( p_variableNumber );
	final KeYJavaType          type = getPartitionType(p_variableNumber);

	if ( type == null ) {
	    if ( getSVPartitioning().isNative(p_variableNumber) )
		createNativePVCandidates ( svs, p_currentSVI, p_currentSVTI, res );
	    else
		createNewPVCandidates    ( svs, p_currentSVI, p_currentSVTI, res );
	} else
	    createNewPVCandidate     ( svs, type, p_currentSVI, p_currentSVTI,
				       res, ProgramSkolemInstantiation
				       .NEW_BOUND_VARIABLE );

	return (PVCandidate[])res.collect ( PVCandidate.class );
    }

    private void createNativePVCandidates ( ImmutableList<SchemaVariable> p_svs,
					    SVInstantiations     p_currentSVI,
					    SVTypeInfos          p_currentSVTI,
					    ExtList              p_res ) {
	final Iterator<IProgramVariable> nativeIt =
	    rpvp.getFreeProgramVariables ().iterator ();

	while ( nativeIt.hasNext () ) {
	    final IProgramVariable pv = nativeIt.next ();

	    final PVCandidate pvc =
	        isValidInstantiation ( p_currentSVI, p_currentSVTI, 
				       p_svs, pv,
				       ProgramSkolemInstantiation
				       .OCCURRING_VARIABLE );
	    if ( pvc != null )
		p_res.add ( pvc );
	}
    }


    private void createNewPVCandidates ( ImmutableList<SchemaVariable> p_svs,
					 SVInstantiations     p_currentSVI,
					 SVTypeInfos          p_currentSVTI,
					 ExtList              p_res ) {
	final Iterator<KeYJavaType> typeIt = createTypeCandidates ();

	while ( typeIt.hasNext () )
	    createNewPVCandidate ( p_svs,
				   typeIt.next (),
				   p_currentSVI,
				   p_currentSVTI,
				   p_res,
				   ProgramSkolemInstantiation.NEW_FREE_VARIABLE );
    }

    private void createNewPVCandidate ( ImmutableList<SchemaVariable> p_svs,
					KeYJavaType          p_type,
					SVInstantiations     p_currentSVI,
					SVTypeInfos          p_currentSVTI,
					ExtList              p_res,
					int                  p_instantiationType ) {
        final IProgramVariable pv  =
            new LocationVariable ( new ProgramElementName ("x"), p_type );

	final PVCandidate      pvc =
	    isValidInstantiation ( p_currentSVI, p_currentSVTI,
				   p_svs, pv,
				   p_instantiationType );

	if ( pvc != null )
	    p_res.add ( pvc );
    }


    private PVCandidate
	isValidInstantiation ( SVInstantiations     p_currentSVI,
			       SVTypeInfos          p_currentSVTI,
			       ImmutableList<SchemaVariable> p_svs,
			       IProgramVariable     p_pv,
			       int                  p_instantiationType ) {

	if ( !StaticCheckerSVI.isValidType ( getOriginalFormula (),
					     p_currentSVI,
					     p_svs,
					     p_pv,
					     getServices () ) )
	    return null;

	final SVInstantiations svi =
	    StaticCheckerSVI.addInstantiation ( p_currentSVI, p_svs, p_pv,
						p_instantiationType );

	if ( svi == null )
	    return null;

	final Iterator<SchemaVariable> it   = p_svs.iterator ();
	SVTypeInfos                    svti = p_currentSVTI;
	while ( it.hasNext () )
	    svti = svti.addInfo ( new SVTypeInfo ( it.next (),
						   p_pv.getKeYJavaType () ) );

	return new PVCandidate ( p_pv, svi, svti );
    }


    /**
     * Remove from the given set of skolem sets those which are
     * subsumed by others, return the remaining ones
     */
    private Iterator<SkolemSet>	handleSubsumption ( Iterator<SkolemSet> p_it ) {
	ImmutableList<SkolemSet>     res       = ImmutableSLList.<SkolemSet>nil();
	Iterator<SkolemSet> compareIt;
	SkolemSet           ss;
	SkolemSet           compareSS;
	
	mainloop:
        while ( p_it.hasNext () ) {
	    ss        = p_it.next ();
	    compareIt = res.iterator ();
	    res       = ImmutableSLList.<SkolemSet>nil();

	    while ( compareIt.hasNext () ) {
		compareSS = compareIt.next ();
		
		switch ( compare ( ss, compareSS ) ) {
		case -1:
		    // ss may be removed
		    res = res.prepend ( compareSS );
		    while ( compareIt.hasNext () )
			res = res.prepend ( compareIt.next () );
		    continue mainloop;

		case 0:
		    res = res.prepend ( compareSS );
		    break;

		case 1:
		    // compareSS may be removed
		    break;
		}
	    }

	    res = res.prepend ( ss );
	}

	return res.iterator ();
    }

    /**
     * @return <code>0</code> if <code>p_a</code> and <code>p_b</code>
     * are not in relation, <code>-1</code> if <code>p_a</code> is
     * subsumed by <code>p_b</code>, <code>1</code> if
     * <code>p_a</code> subsumes <code>p_b</code>
     */
    private int compare ( SkolemSet p_a,
			  SkolemSet p_b ) {
	int                res    = 0;

	int                i      = getSVPartitioning().size ();
	final KeYJavaType  object = getObjectKeYJavaType ( );

	while ( i-- != 0 ) {
	    KeYJavaType    akjt =
	        getSVPartitioning().getType(i, p_a.getSVTypeInfos());
	    KeYJavaType    bkjt =
	        getSVPartitioning().getType(i, p_b.getSVTypeInfos());
	    
	    if ( getSVPartitioning().isNative(i) ) {
	        // for native partitions, only instantiation with the
	        // same type is allowed for subsumption 
	    	if ( akjt == bkjt )
	    	    continue;
	    	return 0;
	    }
	    
	    switch ( res ) {
	    case -1:
		if ( bkjt == object || akjt == bkjt )
		    break;
		return 0;

	    case 0:
		if ( akjt == object ) {
		    if ( bkjt != object )
			res = 1;
		} else {
		    if ( bkjt == object )
			res = -1;
		    else if ( akjt != bkjt )
			return 0;
		}
		break;

	    case 1:
		if ( akjt == object || akjt == bkjt )
		    break;
		return 0;
	    }
	}

	return res;
    }

    private static class PVCandidate {
	public final IProgramVariable pv;
	public final SVInstantiations svi;
	public final SVTypeInfos      svti;

	public PVCandidate ( IProgramVariable p_pv,
			     SVInstantiations p_svi,
			     SVTypeInfos      p_svti ) {
	    pv   = p_pv;
	    svi  = p_svi;
	    svti = p_svti;
	}
    }

}
