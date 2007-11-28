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

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayOfKeYJavaType;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;


/**
 * Factory to create skolem symbols for statements
 */
public class StatementSkolemSymbolFactory extends SkolemSymbolTacletFactory {

    public StatementSkolemSymbolFactory(Services p_services) {
        super(p_services);
    }

    /**
     * Create a skolem symbol for statements
     * @param p_name name of the symbol
     * @param p_influencingPVs program variable arguments the symbol is to
     * be given. A selector variable of type int is added as the last argument
     * implicitly
     * @param jumpTable the jump table that symbol should have
     */
    public ProgramSVProxy createStatementSymbol
        (ProgramElementName     p_name,
         ListOfIProgramVariable p_influencingPVs,
         ArrayOfStatement       p_jumpTable) {
	return createStatementSymbolWithoutSelector
	    (p_name,
	     p_influencingPVs.append(createSelectorVariable()),
	     p_jumpTable);
    }

    /**
     * Like <code>createStatementSymbol</code>, but assume that the last
     * program variable argument already is a valid selector variable
     * (of type int)
     */
    public ProgramSVProxy createStatementSymbolWithoutSelector
        (ProgramElementName     p_name,
         ListOfIProgramVariable p_influencingPVs,
         ArrayOfStatement       p_jumpTable) {
        Debug.assertTrue ( checkSelectorVariable ( p_influencingPVs ),
                           "Last program variable argument is not an " +
                           "admissible selector variable" );
         	
        final ProgramSVProxy proxy = createStatementSymbol
            ( p_name,
              getProgramVariableTypes    ( p_influencingPVs ),
              getProgramVariablesAsArray ( p_influencingPVs ),
              p_jumpTable );
        createDecompositionTaclets ( proxy );
        
        return proxy;
    }

    private ProgramSVProxy createStatementSymbol
	( ProgramElementName      p_name,
	  ArrayOfKeYJavaType      p_influencingPVTypes,
	  ArrayOfIProgramVariable p_influencingPVs,
	  ArrayOfStatement        p_jumpTable ) {
	
	final ProgramSVSkolemStatement sk =
	    new ProgramSVSkolemStatement ( p_name,
	                                   p_influencingPVTypes,
	                                   p_jumpTable.size () );

	final ProgramSVProxy pr = new ProgramSVProxy ( sk,
	                                               p_influencingPVs,
	                                               p_jumpTable );

	return pr;

    }

    private void createDecompositionTaclets ( ProgramSVProxy p ) {
	ExtList   ifJumpTable   = new ExtList ();
	ExtList   findProxy     = new ExtList ();
	ExtList   rwProxy       = new ExtList ();
	createSepSymbol ( p, findProxy, rwProxy, ifJumpTable );
	JavaBlock findJB        = JavaBlock.createJavaBlock
	    ( new ContextStatementBlock    ( findProxy ) );
	JavaBlock sepJB         = JavaBlock.createJavaBlock
	    ( new StatementBlock ( rwProxy ) );
	JavaBlock replaceJB     = JavaBlock.createJavaBlock
	    ( new ContextStatementBlock    ( ifJumpTable ) );

	createTaclets ( findJB,
			replaceJB,
			sepJB,
			"" + p.op ().getProgramElementName () + "_sep" );
    }

    /**
     * Create an additional skolem symbol that can be used for the program
     * decomposition rule. Also create the statements necessary for the rule
     * @param p the primary symbol
     * @param p_findProxy list to which the statement is added on which the
     * decomposition rule applies
     * @param p_rwProxy list to which the statement is added that replaces the
     * primary statement when applying the decomposition rule
     * @param p_ifJumpTable list to which the if-cascade is added which is
     * inserted by the decomposition rule
     */
    private void createSepSymbol ( ProgramSVProxy p,
			           ExtList        p_findProxy,
				   ExtList        p_rwProxy,
				   ExtList        p_jumpCascade ) {
	ProgramElementName      name   = new ProgramElementName
	    ( "" + p.op ().getProgramElementName () + "_sep" );

	ArrayOfIProgramVariable pvs    = createSVsForInfluencingPVs ( p );

	final IProgramVariable  sel    = pvs.getIProgramVariable(pvs.size()-1);

	Statement[]             findJT =
	    createJumpCascade ( p.getJumpTable ().size (), p_jumpCascade, sel );

	p_findProxy.add ( new ProgramSVProxy ( p.op (),
					       pvs,
					       new ArrayOfStatement ( findJT ) ) );
	p_rwProxy  .add ( createStatementSymbol
	                      ( name,
                                p.op ().getInfluencingPVTypes (),
                                pvs,
                                new ArrayOfStatement ( new Statement [ 0 ] ) ) );
    }

    /**
     * Create an if-cascade that dispatches the different abrupt exists given
     * by the jump table of a skolem symbol occurrence. The jump statements
     * are represented by schema variables for statements
     * @param p_size the size of the if-cascade, i.e. the number of schema
     * variables that should be inserted
     * @param p_jumpCascade list to which the result is to be added
     * @param p_sel the program variable that selects the chosen exit
     * @return an array that holds the schema variables used to construct the
     * if-cascade
     */
    private Statement[] createJumpCascade ( int              p_size,
					    ExtList          p_jumpCascade,
					    IProgramVariable p_sel ) {
	int               i       = p_size;
	final Statement[] findJT  = new Statement [ p_size ];
	If                cascade = null;

	while ( i-- != 0 )
            cascade = addBranch(p_sel, findJT, i, cascade);

	if ( cascade != null )
	    p_jumpCascade.add ( cascade );

	return findJT;
    }

    private If addBranch(IProgramVariable p_sel,
                         Statement[]      findJT,
                         int              branchNum,
                         If               oldTop) {
        final SchemaVariable stmtSV  =
            SchemaVariableFactory.createProgramSV ( createUniquePEName("stmt"),
                                                    ProgramSVSort.STATEMENT,
                                                    false );
        findJT[branchNum] = (Statement)stmtSV;
        
        final Then thenLeg = new Then ( (Statement)stmtSV );

        final ExtList compOps = new ExtList ();
        compOps.add ( p_sel );
        compOps.add ( new IntLiteral ( branchNum ) );
        final If newTop = new If ( new Equals ( compOps ), thenLeg );
        
        if ( oldTop != null )
            newTop.addBranch ( new Else ( oldTop ) );
        
        return newTop;
    }

    private boolean checkSelectorVariable
        ( ListOfIProgramVariable p_influencingPVs ) {
         while ( p_influencingPVs.size () > 1 )
             p_influencingPVs = p_influencingPVs.tail ();
         return p_influencingPVs.size () != 0 &&
             p_influencingPVs.head ().getKeYJavaType() == getSelectorType(); 
    }

}
