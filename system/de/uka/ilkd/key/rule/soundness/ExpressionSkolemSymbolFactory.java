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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.util.ExtList;


public class ExpressionSkolemSymbolFactory extends SkolemSymbolTacletFactory {

    public ExpressionSkolemSymbolFactory(Services p_services) {
        super(p_services);
    }

    /**
     * Create a skolem symbol for expressions
     * @param p_name name of the symbol
     * @param p_type result type the symbol shall have
     * @param p_influencingPVs program variable arguments the symbol is to
     * be given. A result variable of type <code>p_type</code> and a 
     * selector variable of type int are added as the last two arguments
     * implicitly
     * @param p_jumpTable the jump table that symbol should have
     */
    public ProgramSVProxy createExpressionSymbol
	( ProgramElementName     p_name,
	  KeYJavaType            p_type,
	  ImmutableList<IProgramVariable> p_influencingPVs,
	  ImmutableArray<Statement>       p_jumpTable ) {
	
	final ImmutableList<IProgramVariable> influencingPVs =
	    p_influencingPVs
	    .append ( createResultVariable(p_type) )
	    .append ( createSelectorVariable() );
	
	final ProgramSVProxy pr = createExpressionSymbol
	    ( p_name,
	      p_type,
	      getProgramVariableTypes    ( influencingPVs ),
	      getProgramVariablesAsArray ( influencingPVs ),
	      p_jumpTable );
	createExpressionTaclets ( pr );
	
	return pr;
    }

    private ProgramSVProxy createExpressionSymbol
	( ProgramElementName      p_name,
	  KeYJavaType             p_type,
	  ImmutableArray<KeYJavaType>      p_influencingPVTypes,
	  ImmutableArray<IProgramVariable> p_influencingPVs,
	  ImmutableArray<Statement>        p_jumpTable ) {
	
	final ProgramSVSkolemExpression sk = new ProgramSVSkolemExpression
	    ( p_name,
	      p_type,
	      p_influencingPVTypes,
	      p_jumpTable.size () );

	final ProgramSVProxy            pr = new ProgramSVProxy
	    ( sk,
	      p_influencingPVs,
	      p_jumpTable );

	return pr;

    }

    private void createExpressionTaclets ( ProgramSVProxy p ) {
	ExtList   findProxy     = new ExtList ();
	ExtList   rwProxy       = new ExtList ();
	createNormSymbols ( p, findProxy, rwProxy );

	JavaBlock findJB        = JavaBlock.createJavaBlock
	    ( new ContextStatementBlock ( findProxy ) );
	JavaBlock replaceJB     = JavaBlock.createJavaBlock
	    ( new ContextStatementBlock ( rwProxy ) );

	createTaclets ( findJB,
			replaceJB,
			"" + p.op ().getProgramElementName () + "_expr" );
    }

    /**
     * Create a statement symbol that is used for the expression
     * normalization rule: An expression symbol is replaced with a statement
     * symbol and an assignment
     * @param p the primary symbol
     * @param p_findStatement list to which the statement is added on which the
     * normalization rule applies (assignment of the expression symbol to a
     * program variable)
     * @param p_rwStatement list to which the statements are added that replace
     * the primary statement when applying the normalization rule
     */
    private void createNormSymbols ( ProgramSVProxy p,
	                             ExtList        p_findStatement,
	                             ExtList        p_rwStatement ) {
	SchemaVariable          lhs       =
	    SchemaVariableFactory.createProgramSV ( createUniquePEName("pv"),
						    ProgramSVSort.VARIABLE,
						    false );

	ImmutableArray<IProgramVariable> pvs       = createSVsForInfluencingPVs ( p );
        IProgramVariable        retVal    = pvs.get(pvs.size()-2);

	ImmutableArray<Statement>        findJT    =
	    new ImmutableArray<Statement> ( createSVsForJumpTable ( p ) );

	ProgramSVProxy          findProxy =
	    new ProgramSVProxy ( p.op (), pvs, findJT );

	ProgramSVProxy          rwProxy   = createNormSymbol ( p, pvs, findJT );

	p_findStatement.add ( new CopyAssignment ( (Expression)lhs, findProxy ) );

	p_rwStatement  .add ( rwProxy );
	p_rwStatement  .add ( new CopyAssignment ( (Expression)lhs,
	                                           (Expression)retVal ) );	
    }

    private Statement[] createSVsForJumpTable ( ProgramSVProxy p ) {
	final Statement[] findJT  = new Statement [ p.getJumpTable ().size () ];
	int         i       = p.getJumpTable ().size ();

	while ( i-- != 0 )
	    findJT[i] = (Statement)SchemaVariableFactory.createProgramSV
		( createUniquePEName("stmt"),
		  ProgramSVSort.STATEMENT,
		  false );

	return findJT;
    }

    private ProgramSVProxy
	createNormSymbol ( ProgramSVProxy p,
	                   ImmutableArray<IProgramVariable> p_influencingPVs,
			   ImmutableArray<Statement>        p_jumpTable ) {
	final String baseName = "" + p.op ().getProgramElementName () + "_expr";
	
	final ImmutableList<IProgramVariable> pvArgs =
	    getProgramVariablesAsList ( p.getInfluencingPVs() );
	
	final ProgramSVProxy statement =
	    createStatementSymbol(baseName, pvArgs, p.getJumpTable());
	
	// Replace arguments and jump table with the given schema variables
	final ImmutableArray<IProgramVariable> svArgs =
	    getProgramVariablesAsArray
		( getProgramVariablesAsList ( p_influencingPVs ) );
	
	return new ProgramSVProxy ( statement.op (), svArgs, p_jumpTable );
    }

    /**
     * Use the statement symbol factory to create the necessary statement symbol
     * for the normalization rule
     */
    private ProgramSVProxy
        createStatementSymbol ( String                 p_baseName,
                                ImmutableList<IProgramVariable> p_influencingPVs,
                                ImmutableArray<Statement>       p_jumpTable) {
	final StatementSkolemSymbolFactory f =
	    new StatementSkolemSymbolFactory ( getServices() );

        final ProgramSVProxy     proxy =
            f.createStatementSymbolWithoutSelector(createUniquePEName(p_baseName),
                                                   p_influencingPVs,
                                                   p_jumpTable);
          
        addVocabulary(f);
        
        return proxy;
    }

    private ProgramVariable createResultVariable(KeYJavaType retType) {
        final ProgramVariable retVal = new LocationVariable
            ( createUniquePEName("ret"), retType );
        addVariable(retVal);
        return retVal;
    }

}
