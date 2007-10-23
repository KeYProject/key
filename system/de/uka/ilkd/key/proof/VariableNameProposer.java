// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.proof;

import java.util.HashSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.LabelCollector;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Proposes names for variables (except program variables).
 */
public class VariableNameProposer implements InstantiationProposer {

    /**
     * An instance of VariableNameProposer.
     */
    public static final VariableNameProposer DEFAULT 
    				= new VariableNameProposer();

    private static final String SKOLEMTERM_VARIABLE_NAME_POSTFIX = "_";
    private static final String VARIABLE_NAME_PREFIX             = "_var";
    private static final String LABEL_NAME_PREFIX                = "_label";

    private static final String GENERALNAMECOUNTER_PREFIX   = "GenCnt";
    private static final String SKOLEMTERMVARCOUNTER_PREFIX = "DepVarCnt";
    private static final String VARCOUNTER_NAME 	        = "VarCnt";
    private static final String LABELCOUNTER_NAME 	        = "LabelCnt";


    /**
     * Returns an instantiation proposal for the schema variable var.
     * Currently supports names for skolemterm SVs, variable SVs, and labels.
     */
    public String getProposal(TacletApp app,
    			      SchemaVariable var,
			      Services services,
			      Node undoAnchor,
			      ListOfString previousProposals) {
	if(var.isSkolemTermSV()) {
	    return getNameProposalForSkolemTermVariable(app,
	    					       var,
						       services,
						       undoAnchor,
                                                       previousProposals);
	} else if(var.isVariableSV()) {
	    return getNameProposalForVariableSV(app,
	    					var,
						services,
						undoAnchor);
	} else if(((SortedSchemaVariable)var).sort() == ProgramSVSort.LABEL) {
	    return getNameProposalForLabel(app,
	    				   var,
					   services,
					   undoAnchor,
                                           previousProposals);
	} else {
	    return null;
	}
    }


    /**
     * Generates a proposal for the instantiation of the given term
     * schema variable, which is declared as skolem term SV.
     */
    private String getNameProposalForSkolemTermVariable(TacletApp p_app,
    						       SchemaVariable p_var,
						       Services services,
						       Node undoAnchor,
                                                       ListOfString previousProposals) {
	return getNameProposalForSkolemTermVariable
	    ( createBaseNameProposalBasedOnCorrespondence ( p_app, p_var ),
	      services,
	      undoAnchor,
              previousProposals);
    }


    /**
     * Find a name for the variable <code>p_var</code>, based on the result
     * of <code>Taclet.getNameCorrespondent</code>
     */
    protected static String createBaseNameProposalBasedOnCorrespondence (TacletApp p_app,
                                                                         SchemaVariable p_var) {
        final String result;
        final SchemaVariable v = p_app.taclet ().getNameCorrespondent ( p_var );
        if ( v != null && p_app.instantiations ().isInstantiated ( v ) ) {
            
            final Object inst = p_app.instantiations ().getInstantiation ( v );
            
            if (inst instanceof Term) {
                result = ((Term)inst).op().name().toString();
            } else {
                result = "" + inst;
            }
        } else {
            // ... otherwise use the name of the SkolemTermSV
            result = "" + p_var.name ();
        }

        // remove characters that should better not turn up in identifiers
        // more or less a HACK
        final Pattern pattern = Pattern.compile ( "[^_a-zA-Z0-9]" );
        final Matcher matcher = pattern.matcher ( result );

        final Pattern doubledUnderScores = Pattern.compile ( "__" );

        return doubledUnderScores.matcher(matcher.replaceAll ( "_" )).replaceAll("");
    }


    private String getNameProposalForSkolemTermVariable(String name,
    						       Services services,
						       Node undoAnchor,
                                                       ListOfString previousProposals) {

	final NamespaceSet nss = services.getNamespaces();
	Name l_name;
	final String basename = name + SKOLEMTERM_VARIABLE_NAME_POSTFIX;
	do {
	    name = basename + services.getCounter(SKOLEMTERMVARCOUNTER_PREFIX + name)
		.getCountPlusPlusWithParent(undoAnchor);	    
	    l_name = new Name(name);
	} while (nss.lookup(l_name) != null &&
                !previousProposals.contains(name));
        
        	
	return name;
    }

    public String getNameProposal(String basename, 
            Services services, Node undoAnchor) {
        final NamespaceSet nss = services.getNamespaces();
        Name l_name;
        String name = "";
        do {
            if (name.length() > 0) {
                name = basename + 
                services.getCounter(GENERALNAMECOUNTER_PREFIX + name)
                .getCountPlusPlusWithParent(undoAnchor);
            } else {
                name = basename.length() > 0 ? basename : "gen";
            }
            l_name = new Name(name);
        } while (nss.lookup(l_name) != null);
        
        return name;
    }

    /**
     * Generates a proposal for the instantiation of the given
     * schema variable, which is a variable SV.
     */
    private String getNameProposalForVariableSV(TacletApp app,
						SchemaVariable var,
						Services services,
						Node undoAnchor) {
	return VARIABLE_NAME_PREFIX + services.getCounter(VARCOUNTER_NAME)
	  				      .getCountPlusPlusWithParent(undoAnchor);
    }


    /**
     * Generates a proposal for the instantiation of the given
     * schema variable, which is of sort label.
     * @param previousProposals 
     */
    private String getNameProposalForLabel(TacletApp app,
					   SchemaVariable var,
					   Services services,
					   Node undoAnchor,
                                           ListOfString previousProposals) {       
	        
        ProgramElement contextProgram =
            app.matchConditions().getInstantiations().
            getContextInstantiation().contextProgram();
        
        if (contextProgram == null) 
                contextProgram = new StatementBlock();
        
        final LabelCollector lc = 
            new LabelCollector(contextProgram, new HashSet(10));

        lc.start();
        String proposal;         
        do {
            proposal = LABEL_NAME_PREFIX + services.getCounter(LABELCOUNTER_NAME)
            .getCountPlusPlusWithParent(undoAnchor);
        } while (lc.contains(new ProgramElementName(proposal)) ||
                previousProposals.contains(proposal));
        
        return proposal;
    }
}
