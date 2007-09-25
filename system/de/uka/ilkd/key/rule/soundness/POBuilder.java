// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.rule.ListOfTacletApp;
import de.uka.ilkd.key.rule.SLListOfTacletApp;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.TacletApp;


public class POBuilder {

    private final TacletApp            app;
    private final Namespace            functions;
    private final Namespace            variables;
    private final Services             services;

    private ListOfTacletApp            taclets;
    private Term                       meaningTerm;
    private Term                       poTerm;
    private int                        numberOfPOParts = 0;
    
    private JumpStatementPrefixes      jsp;
    private ProgramVariablePrefixes    pvp;
    private RawProgramVariablePrefixes rpvp;

    private boolean                    contextFitting;

    private final Logger               logger          =
                    Logger.getLogger ( "key.taclet_soundness" );
    

    public POBuilder ( TacletApp p_app,
		       Services  p_services ) {
	app       = p_app;
	services  = p_services;
	poTerm    = null;
	functions = new Namespace ();
	variables = new Namespace ();
	taclets   = SLListOfTacletApp.EMPTY_LIST;
    }

    public void build () {
	buildMeaningTerm ();

	SkolemSet ss = new SkolemSet.DefaultSkolemSet ( getTacletApp   (),
							getMeaningTerm () );

	buildContext ( ss );
    }

    private void buildContext ( SkolemSet p_ss ) {
	SkolemBuilder       sb = new ContextSkolemBuilder ( p_ss,
							    getServices () );
	IteratorOfSkolemSet it = sb.build ();

	while ( it.hasNext () ) {
	    contextFitting = false;

	    buildLabels ( it.next () );

	    if ( contextFitting )
		// It's not necessary to use different result types
		// for the method frame, so we just use the first one
		// leading to correct results
		break;
	}
    }

    private void buildLabels ( SkolemSet p_ss ) {
	SkolemBuilder       sb =
	    new LabelSkolemBuilder ( p_ss, getServices () );
	IteratorOfSkolemSet it = sb.build ();

	while ( it.hasNext () )
	    buildLogicVariables ( it.next () );
    }

    private void buildLogicVariables ( SkolemSet p_ss ) {
	SkolemBuilder       sb =
	    new LogicVariableSkolemBuilder ( p_ss, getServices () );
	IteratorOfSkolemSet it = sb.build ();

	while ( it.hasNext () )
	    buildPartitioning ( it.next () );
    }

    private void buildPartitioning ( SkolemSet p_ss ) {
        p_ss = collectPrefixes(p_ss);

	SkolemBuilder       sb = new SVPartitioningBuilder
	    ( p_ss, getRawProgramVariablePrefixes(), getServices () );
	IteratorOfSkolemSet it = sb.build ();

	while ( it.hasNext () )
	    buildTypeInfos ( it.next () );
    }

    private void buildTypeInfos ( SkolemSet p_ss ) {
	SkolemBuilder       sb =
	    new TypeInfoBuilder ( p_ss,
				  getRawProgramVariablePrefixes (),
				  getServices () );
	IteratorOfSkolemSet it = sb.build ();

	while ( it.hasNext () )
	    buildProgramVariables ( it.next () );
    }

    private void buildProgramVariables ( SkolemSet p_ss ) {
	SkolemBuilder       sb =
	    new ProgramVariableSkolemBuilder ( p_ss,
					       getRawProgramVariablePrefixes (),
					       getServices () );
	IteratorOfSkolemSet it = sb.build ();

	while ( it.hasNext () ) {
	    final SkolemSet ss = it.next (); 
	    instantiatePrefixes(ss);
	    buildFunctions ( ss );
	}
    }

    private void buildFunctions        ( SkolemSet p_ss ) {
	SkolemBuilder       sb =
	    new FunctionSkolemBuilder ( getTacletApp ().taclet (),
					p_ss,
					getProgramVariablePrefixes (),
					getServices () );
	IteratorOfSkolemSet it = sb.build ();	

	while ( it.hasNext () )
	    buildStatements ( it.next () );
    }

    private void buildStatements       ( SkolemSet p_ss ) {
	SkolemBuilder       sb =
	    new StatementSkolemBuilder ( p_ss,
					 getProgramVariablePrefixes (),
					 getJumpStatementPrefixes (),
					 getServices () );
	IteratorOfSkolemSet it = sb.build ();

	while ( it.hasNext () )
	    buildExpressions ( it.next () );
    }

    private void buildExpressions      ( SkolemSet p_ss ) {
	SkolemBuilder       sb =
	    new ExpressionSkolemBuilder ( p_ss,
					  getProgramVariablePrefixes (),
					  getJumpStatementPrefixes (),
					  getServices () );
	IteratorOfSkolemSet it = sb.build ();

	while ( it.hasNext () )
	    addPOPart ( it.next () );
    }

    private void buildMeaningTerm () {
    	final MeaningFormulaBuilder b =
    	    new MeaningFormulaBuilder ( getTacletApp() );

	meaningTerm = b.build ();
	logger.debug("Meaning formula: " + meaningTerm);
    }

    private void addPOPart ( SkolemSet p_skolemSet ) {
	contextFitting = true;
	++numberOfPOParts;

	logger.debug("addPOPart() with " + p_skolemSet.getInstantiations ());
        addPOPart(createPOPart(p_skolemSet));

        copyNamespace(p_skolemSet.getFunctions (), functions);
	copyNamespace(p_skolemSet.getVariables (), variables);

	taclets = taclets.prepend ( p_skolemSet.getTaclets () );
    }

    private Term createPOPart(SkolemSet p_skolemSet) {
        SyntacticalReplaceVisitor srv = new SyntacticalReplaceVisitor
            ( getServices (), p_skolemSet.getInstantiations () );
        p_skolemSet.getFormula ().execPostOrder ( srv );

        return srv.getTerm ();
    }

    private void addPOPart(Term p_formula) {
        if ( poTerm == null )
            poTerm = p_formula;
        else
            poTerm = TermFactory.DEFAULT.createJunctorTerm
        	( Op.AND, p_formula, poTerm );
    }

    private SkolemSet collectPrefixes(SkolemSet p_ss) {
	SVPrefixCollectorSVI c = new SVPrefixCollectorSVI ( p_ss.getInstantiations (),
							    p_ss.getSVTypeInfos (),
							    getServices () );
	c.collect ( p_ss.getFormula () );
	jsp  = c.getJumpStatementPrefixes   ();
	rpvp = c.getRawProgramVariablePrefixes ();
	p_ss = p_ss.setSVTypeInfos ( c.getSVTypeInfos () );
	logger.debug ( "Free schema variables: "
                + rpvp.getFreeSchemaVariables () );
        logger.debug ( "Bound schema variables: "
                + rpvp.getBoundSchemaVariables () );
        logger.debug ( "Free program variables: "
                + rpvp.getFreeProgramVariables () );

        return p_ss;
    }

    private void instantiatePrefixes(final SkolemSet ss) {
	pvp = getRawProgramVariablePrefixes ()
	    .instantiate ( ss.getInstantiations () );
	logger.debug ( "instantiatePrefixes() with " + ss.getInstantiations () );
    }

    public Namespace getFunctions () {
	return functions;
    }

    public Namespace getVariables () {
	return variables;
    }

    public ListOfTacletApp getTaclets () {
	return taclets;
    }

    public Term      getPOTerm    () {
	if ( poTerm == null )
	    return TermFactory.DEFAULT.createJunctorTerm ( Op.TRUE );
	else
	    return poTerm;
    }

    public int getNumberOfPOParts() {
        return numberOfPOParts;
    }

    public TacletApp getTacletApp () {
	return app;
    }

    public Services  getServices  () {
	return services;
    }

    private JumpStatementPrefixes getJumpStatementPrefixes () {
	return jsp;
    }

    private ProgramVariablePrefixes getProgramVariablePrefixes () {
	return pvp;
    }

    private RawProgramVariablePrefixes getRawProgramVariablePrefixes () {
	return rpvp;
    }

    private Term getMeaningTerm () {
	return meaningTerm;
    }
    
    private void copyNamespace(Namespace p_source, Namespace p_target) {
	IteratorOfNamed it = p_source.allElements ().iterator ();
	while ( it.hasNext () )
	    p_target.add ( it.next () );
    }
}
