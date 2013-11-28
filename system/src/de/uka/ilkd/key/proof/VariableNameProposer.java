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



package de.uka.ilkd.key.proof;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.LabelCollector;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
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
    private static final String LABEL_NAME_PREFIX                = "_label";

    private static final String GENERALNAMECOUNTER_PREFIX   = "GenCnt";
    private static final String SKOLEMTERMVARCOUNTER_PREFIX = "DepVarCnt";
    private static final String LABELCOUNTER_NAME 	        = "LabelCnt";


    /**
     * Returns an instantiation proposal for the schema variable var.
     * Currently supports names for skolemterm SVs, variable SVs, and labels.
     */
    public String getProposal(TacletApp app,
    			      SchemaVariable var,
			      Services services,
			      Node undoAnchor,
			      ImmutableList<String> previousProposals) {
	if(var instanceof SkolemTermSV) {
	    return getNameProposalForSkolemTermVariable(app,
	    					        var,
						        services,
						        undoAnchor,
                                                        previousProposals);
	} else if(var instanceof VariableSV) {
	    return getNameProposalForVariableSV(app,
	    					var,
						services,
						previousProposals);
	} else if(var.sort() == ProgramSVSort.LABEL) {
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
     * Warning: this method is buggy. It causes problems with proof reloading.
     * Use the method TermBuilder.newName instead.
     */
    public Name getNewName(Services services, Name baseName) {
        NamespaceSet namespaces = services.getNamespaces();

        Name name = services.getNameRecorder().getProposal();            
        if (name == null || namespaces.lookup(name) != null) {
            int i = 0;

            do {
                name = new Name(baseName + "_" + i++);
            } while(namespaces.lookup(name) != null);

        }

        return name;
    }

    /**
     * Generates a proposal for the instantiation of the given term
     * schema variable, which is declared as skolem term SV.
     */
    private String getNameProposalForSkolemTermVariable(TacletApp p_app,
    						        SchemaVariable p_var,
						        Services services,
						        Node undoAnchor,
                                                        ImmutableList<String> previousProposals) {
	return getNameProposalForSkolemTermVariable
	    ( createBaseNameProposalBasedOnCorrespondence ( p_app, p_var, services ),
	      services,
	      undoAnchor,
              previousProposals);
    }


    /**
     * Find a name for the variable <code>p_var</code>, based on the result
     * of <code>Taclet.getNameCorrespondent</code>
     */
    protected static String createBaseNameProposalBasedOnCorrespondence (TacletApp p_app,
                                                                         SchemaVariable p_var,
                                                                         Services services) {
        final String result;
        final SchemaVariable v = p_app.taclet ().getNameCorrespondent ( p_var, services );
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
                                                       ImmutableList<String> previousProposals) {

	final NamespaceSet nss = services.getNamespaces();
	Name l_name;
	final String basename = name + SKOLEMTERM_VARIABLE_NAME_POSTFIX;
	do {
	    name = basename + services.getCounter(SKOLEMTERMVARCOUNTER_PREFIX + name)
		.getCountPlusPlus();	    
	    l_name = new Name(name);
	} while (nss.lookup(l_name) != null &&
                !previousProposals.contains(name));
        
        	
	return name;
    }

    
    public String getNameProposal(String basename, 
	    			  Services services, 
	    			  Node undoAnchor) {
        final NamespaceSet nss = services.getNamespaces();
        Name l_name;
        String name = "";
        do {
            if (name.length() > 0) {
                name = basename + 
                services.getCounter(GENERALNAMECOUNTER_PREFIX + name)
                .getCountPlusPlus();
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
     * 
     * The returned name is not necessarily globally unique, but that is not
     * necessary for bound variables.
     */
    private String getNameProposalForVariableSV(TacletApp app,
						SchemaVariable var,
						Services services,
						ImmutableList<String> previousProposals) {

        String baseName = var.name().toString();
        if(previousProposals == null || !previousProposals.contains(baseName)) {
            return baseName;
        }

        for(int i = 1; i < Integer.MAX_VALUE; i++) {
            String name = baseName + "_" + i;
            if(!previousProposals.contains(name)) {
                return name;
            }
        }

        throw new Error("name proposer for " + baseName + " has run into infinite loop");

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
                                           ImmutableList<String> previousProposals) {       
	        
        ProgramElement contextProgram =
            app.matchConditions().getInstantiations().
            getContextInstantiation().contextProgram();
        
        if (contextProgram == null) 
                contextProgram = new StatementBlock();
        
        final LabelCollector lc = 
            new LabelCollector(contextProgram, services);

        lc.start();
        String proposal;         
        do {
            proposal = LABEL_NAME_PREFIX + services.getCounter(LABELCOUNTER_NAME)
            .getCountPlusPlus();
        } while (lc.contains(new ProgramElementName(proposal)) ||
                previousProposals.contains(proposal));
        
        return proposal;
    }
}
