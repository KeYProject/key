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

import de.uka.ilkd.key.java.ArrayOfStatement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.inst.ProgramSkolemInstantiation;



/**
 * Create expression skolem symbols to instantiate schema variables for
 * expressions
 */
public class ExpressionSkolemBuilder extends StatementExpressionSkolemBuilder {

    public ExpressionSkolemBuilder
	( SkolemSet               p_oriSkolemSet,
	  ProgramVariablePrefixes p_prefixes,
	  JumpStatementPrefixes   p_jumpStatementPrefixes,
	  Services                p_services ) {
	super ( p_oriSkolemSet,
		p_prefixes,
		p_jumpStatementPrefixes,
		p_services );
    }

    public IteratorOfSkolemSet build () {
	ListOfSchemaVariable todo =
	    findExpressionSVs ( getOriginalSkolemSet () );

	return createSkolemExpressionSVs ( todo );
    }

    public static ListOfSchemaVariable findExpressionSVs ( SkolemSet p_ss ) {
	IteratorOfSchemaVariable it =
	    p_ss.getMissing ().iterator ();
	SchemaVariable           sv;
	ListOfSchemaVariable     res = SLListOfSchemaVariable.EMPTY_LIST;

	while ( it.hasNext () ) {
	    sv = it.next ();

	    if ( sv.isProgramSV () &&
		 ((SortedSchemaVariable)sv).sort () == ProgramSVSort.EXPRESSION )
		res = res.prepend ( sv );
	}

	return res;
    }

    private IteratorOfSkolemSet
	createSkolemExpressionSVs(ListOfSchemaVariable p_svs) {    
	IteratorOfSchemaVariable it = p_svs.iterator ();
	while ( it.hasNext () )
	    createSkolemExpressionSV ( it.next () );
    
	return toIterator
	    ( getOriginalSkolemSet ()
	      .add          ( getSVI() )
	      .addVariables ( getVariables() )
	      .addTaclets   ( getTaclets() ) );	
    }

    private void createSkolemExpressionSV(SchemaVariable p_sv) {
	final SVTypeInfo svti =
	    getOriginalSkolemSet ().getSVTypeInfos ().getInfo ( p_sv );
    
	createSkolemExpressionSV ( p_sv, svti.getType () );
    }

    private void createSkolemExpressionSV(SchemaVariable p_sv,
					  KeYJavaType    p_type) {
	final String baseName = "" + p_sv.name () + "_" +
	                        p_type.getJavaType ().getFullName ();
        ProgramElementName name  = createUniquePEName (baseName);
	final StatementSymbolArgBuilder b =
	    new StatementSymbolArgBuilder ( p_sv );
        
	final ProgramSVProxy proxy =
	    createSkolemExpressionSV ( name,
				       p_type,
				       b.getInfluencingPVs(),
				       b.getJumpTable() );
    
        addInstantiation(p_sv, proxy, ProgramSkolemInstantiation.NEW_EXPRESSION);
    }

    private ProgramSVProxy
	createSkolemExpressionSV(ProgramElementName     p_name,
				 KeYJavaType            p_type,
				 ListOfIProgramVariable p_influencingPVs,
				 ArrayOfStatement       p_jumpTable) {
	final ExpressionSkolemSymbolFactory f =
	    new ExpressionSkolemSymbolFactory ( getServices() );
    
        final ProgramSVProxy proxy =
            f.createExpressionSymbol(p_name, p_type, p_influencingPVs, p_jumpTable);
          
        addVocabulary(f);
        
        return proxy;
    }

}
