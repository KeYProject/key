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

import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SetAsListOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SetOfSchemaVariable;
import de.uka.ilkd.key.rule.ListOfTacletApp;
import de.uka.ilkd.key.rule.SLListOfTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;



/**
 * Immutable
 */
public interface SkolemSet {

    SVInstantiations    getInstantiations ();

    Namespace           getFunctions      ();

    Namespace           getVariables      ();

    ListOfTacletApp     getTaclets        ();

    SetOfSchemaVariable getMissing        ();

    Term                getFormula        ();

    SVTypeInfos         getSVTypeInfos    ();

    SVPartitioning      getSVPartitioning ();

    SkolemSet           add ( SVInstantiations    p_inst );

    SkolemSet           addFunctions ( Namespace p_functions );

    SkolemSet           addVariables ( Namespace p_variables );

    SkolemSet           addTaclets   ( ListOfTacletApp p_taclets );

    SkolemSet           addMissing   ( IteratorOfSchemaVariable p_missing );

    SkolemSet           setFormula   ( Term p_formula );

    SkolemSet           setSVTypeInfos ( SVTypeInfos p_infos );

    SkolemSet           setSVPartitioning ( SVPartitioning p_partitioning );

    static class DefaultSkolemSet implements SkolemSet {

	private SVInstantiations    inst;
	private Namespace           functions;
	private Namespace           variables;
	private ListOfTacletApp     taclets;
	private SetOfSchemaVariable miss;
	private Term                formula;
	private SVTypeInfos         svTypeInfos;
	private SVPartitioning      svPartitioning;

	private DefaultSkolemSet ( SVInstantiations    p_inst,
				   Namespace           p_functions,
				   Namespace           p_variables,
				   ListOfTacletApp     p_taclets,
				   SetOfSchemaVariable p_miss,
				   Term                p_formula,
				   SVTypeInfos         p_svTypeInfos,
				   SVPartitioning      p_svPartitioning ) {
	    inst           = p_inst;
	    functions      = p_functions;
	    variables      = p_variables;
	    taclets        = p_taclets;
	    miss           = p_miss;
	    formula        = p_formula;
	    svTypeInfos    = p_svTypeInfos;
	    svPartitioning = p_svPartitioning;
	}

	public DefaultSkolemSet ( TacletApp           p_app,
				  Term                p_formula ) {
	    this ( p_app.instantiations (),
		   new Namespace (),
		   new Namespace (),
		   SLListOfTacletApp.EMPTY_LIST,
		   p_app.uninstantiatedVars (),
		   p_formula,
		   SVTypeInfos.EMPTY_SVTYPEINFOS,
		   null );
	}

	public SkolemSet           addFunctions ( Namespace p_functions ) {
	    Namespace n = new Namespace ( getFunctions () );
	    n.add ( p_functions );
	    return new DefaultSkolemSet ( getInstantiations (),
					  n,
					  getVariables      (),
					  getTaclets        (),
					  getMissing        (),
					  getFormula        (),
					  getSVTypeInfos    (),
					  getSVPartitioning () );
	}

	public SkolemSet           addVariables ( Namespace p_variables ) {
	    Namespace n = new Namespace ( getVariables () );
	    n.add ( p_variables );
	    return new DefaultSkolemSet ( getInstantiations (),
					  getFunctions      (),
					  n,
					  getTaclets        (),
					  getMissing        (),
					  getFormula        (),
					  getSVTypeInfos    (),
					  getSVPartitioning () );
	}

	public SkolemSet           addTaclets ( ListOfTacletApp p_taclets ) {
	    return new DefaultSkolemSet ( getInstantiations (),
					  getFunctions      (),
					  getVariables      (),
					  getTaclets        ()
					  .prepend ( p_taclets ),
					  getMissing        (),
					  getFormula        (),
					  getSVTypeInfos    (),
					  getSVPartitioning () );
	}

	public SkolemSet add ( SVInstantiations p_inst ) {
	    SetOfSchemaVariable      m  = SetAsListOfSchemaVariable.EMPTY_SET;
	    IteratorOfSchemaVariable it = getMissing ().iterator ();
	    SchemaVariable           v;

	    while ( it.hasNext () ) {
		v = it.next ();
		if ( !p_inst.isInstantiated ( v ) )
		    m = m.add ( v );
	    }

	    return new DefaultSkolemSet ( p_inst,
					  getFunctions   (),
					  getVariables   (),
					  getTaclets     (),
					  m,
					  getFormula     (),
					  getSVTypeInfos (),
					  getSVPartitioning () );
	}

	public SkolemSet           addMissing   ( IteratorOfSchemaVariable p_missing ) {
	    SetOfSchemaVariable m = getMissing ();
	    while ( p_missing.hasNext () )
		m = m.add ( p_missing.next () );
	    return new DefaultSkolemSet ( getInstantiations (),
					  getFunctions      (),
					  getVariables      (),
					  getTaclets        (),
					  m,
					  getFormula        (),
					  getSVTypeInfos    (),
					  getSVPartitioning () );
	}

	public SkolemSet           setFormula   ( Term p_formula ) {
	    return new DefaultSkolemSet ( getInstantiations (),
					  getFunctions      (),
					  getVariables      (),
					  getTaclets        (),
					  getMissing        (),
					  p_formula,
					  getSVTypeInfos    (),
					  getSVPartitioning () );
	}

	public SkolemSet           setSVTypeInfos ( SVTypeInfos p_infos ) {
	    return new DefaultSkolemSet ( getInstantiations (),
					  getFunctions      (),
					  getVariables      (),
					  getTaclets        (),
					  getMissing        (),
					  getFormula        (),
					  p_infos,
					  getSVPartitioning () );
	}

	public SVInstantiations    getInstantiations () {
	    return inst;
	}

	public Namespace           getFunctions      () {
	    return functions;
	}	

	public Namespace           getVariables      () {
	    return variables;
	}	

	public ListOfTacletApp     getTaclets        () {
	    return taclets;
	}

	public SetOfSchemaVariable getMissing        () {
	    return miss;
	}

	public Term                getFormula        () {
	    return formula;
	}

	public SVTypeInfos         getSVTypeInfos    () {
	    return svTypeInfos;
	}

        public SVPartitioning      getSVPartitioning () {
            return svPartitioning;
        }

        public SkolemSet setSVPartitioning(SVPartitioning p_partitioning) {
	    return new DefaultSkolemSet ( getInstantiations (),
					  getFunctions      (),
					  getVariables      (),
					  getTaclets        (),
					  getMissing        (),
					  getFormula        (),
					  getSVTypeInfos    (),
					  p_partitioning );
        }

    }

}
