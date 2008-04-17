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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.*;


/**
 * This class provides methods that are used to construct taclets
 * (which are needed to create skolem symbols for statements and
 * expressions)
 */
abstract class SkolemSymbolTacletFactory extends SkolemSymbolFactory {

    private ListOfTacletApp taclets = SLListOfTacletApp.EMPTY_LIST;

    SkolemSymbolTacletFactory(Services p_services) {
        super(p_services);
    }

    /**
     * @return all created taclets
     */
    public ListOfTacletApp getTaclets() {
        return taclets;
    }

    /**
     * Create rewrite taclets that split a Java block in two separate
     * (nested) blocks
     * @param p_find the block to rewrite
     * @param p_replace the inner replacement block 
     * @param p_sep the outer replacement block
     * @param p_name base name of the taclets
     */
    protected void createTaclets ( JavaBlock p_find,
				   JavaBlock p_replace,
				   JavaBlock p_sep,
				   String    p_name ) {
	createBoxTaclet     ( p_find, p_replace, p_sep, p_name );
	createDiamondTaclet ( p_find, p_replace, p_sep, p_name );
    }

    private void createBoxTaclet ( JavaBlock p_find,
				   JavaBlock p_replace,
				   JavaBlock p_sep,
				   String    p_name ) {
	SchemaVariable post =
	    SchemaVariableFactory.createFormulaSV ( new Name ( "post" ), false );
	Term           find =
	    getTF().createBoxTerm ( p_find,
			       getTF().createVariableTerm ( post ) );
	Term           rw   =
	    getTF().createBoxTerm ( p_sep,
			       getTF().createBoxTerm
			       ( p_replace,
				 getTF().createVariableTerm ( post ) ) );

	createTaclet ( find, rw, p_name + "_box" );
    }

    private void createDiamondTaclet ( JavaBlock p_find,
				       JavaBlock p_replace,
				       JavaBlock p_sep,
				       String    p_name ) {
	SchemaVariable post =
	    SchemaVariableFactory.createFormulaSV ( new Name ( "post" ), false );
	Term           find =
	    getTF().createDiamondTerm ( p_find,
				   getTF().createVariableTerm ( post ) );
	Term           rw   =
	    getTF().createDiamondTerm ( p_sep,
				   getTF().createDiamondTerm
				   ( p_replace,
				     getTF().createVariableTerm ( post ) ) );

	createTaclet ( find, rw, p_name + "_dia" );
    }

    /**
     * Create taclets that rewrite a Java block
     * @param p_find the block to rewrite
     * @param p_replace the new block
     * @param p_name base name of the taclets
     */
    protected void createTaclets ( JavaBlock p_find,
				   JavaBlock p_replace,
				   String    p_name ) {
	createBoxTaclet     ( p_find, p_replace, p_name );
	createDiamondTaclet ( p_find, p_replace, p_name );
    }

    private void createBoxTaclet ( JavaBlock p_find,
				   JavaBlock p_replace,
				   String    p_name ) {
	SchemaVariable post =
	    SchemaVariableFactory.createFormulaSV ( new Name ( "post" ), false );
	Term           find =
	    getTF().createBoxTerm ( p_find,
			       getTF().createVariableTerm ( post ) );
	Term           rw   =
	    getTF().createBoxTerm ( p_replace,
			       getTF().createVariableTerm ( post ) );

	createTaclet ( find, rw, p_name + "_box" );
    }

    private void createDiamondTaclet ( JavaBlock p_find,
				       JavaBlock p_replace,
				       String    p_name ) {
	SchemaVariable post =
	    SchemaVariableFactory.createFormulaSV ( new Name ( "post" ), false );
	Term           find =
	    getTF().createDiamondTerm ( p_find,
				   getTF().createVariableTerm ( post ) );
	Term           rw   =
	    getTF().createDiamondTerm ( p_replace,
				   getTF().createVariableTerm ( post ) );

	createTaclet ( find, rw, p_name + "_dia" );
    }

    private void createTaclet ( Term   p_find,
				Term   p_rw,
				String p_name ) {
	RewriteTacletBuilder builder = new RewriteTacletBuilder ();

	builder.setFind ( p_find );

	RewriteTacletGoalTemplate goal = new RewriteTacletGoalTemplate
	    ( Sequent.EMPTY_SEQUENT,
	      SLListOfTaclet.EMPTY_LIST,
	      p_rw );
	builder.addTacletGoalTemplate ( goal );
	
	builder.setName ( new Name ( p_name ) );

	taclets = taclets.prepend ( NoPosTacletApp.createNoPosTacletApp
				    ( builder.getTaclet () ) );
    }

    /**
     * Create an array of PVSV which is compatible to the
     * program variable arguments of <code>p</code>
     */
    protected ArrayOfIProgramVariable
	createSVsForInfluencingPVs ( ProgramSVProxy p ) {

	int                i   = p.getInfluencingPVs ().size ();
	IProgramVariable[] res = new IProgramVariable [ i ];

	while ( i-- != 0 )
	    res[i] = (IProgramVariable)SchemaVariableFactory
		.createProgramSV ( createUniquePEName("pv"),
				   ProgramSVSort.VARIABLE,
				   false );
	
	return new ArrayOfIProgramVariable ( res );
    }

    protected void addVocabulary(SkolemSymbolFactory p) {
        super.addVocabulary(p);
	if ( p instanceof SkolemSymbolTacletFactory )
	    taclets = taclets.prepend ( ((SkolemSymbolTacletFactory)p).taclets );
    }

    protected ProgramVariable createSelectorVariable() {
        final ProgramVariable sel = new LocationVariable
            ( createUniquePEName("sel"), getSelectorType() );
        addVariable ( sel );
        return sel;
    }

    protected KeYJavaType getSelectorType() {
        return getJavaInfo ().getPrimitiveKeYJavaType ( "int" );
    }

}
