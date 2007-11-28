// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;

/**
 * This visitor is used to collect information about schema variable
 * pairs occurring within the same substitution operator within a
 * taclet. This information is used to choose names of metavariables
 * or skolem functions.
 */

public class SVNameCorrespondenceCollector extends Visitor {

    /**
     * This map contains (a, b) if there is a substitution {b a}
     * somewhere in the taclet
     */
    private MapFromSchemaVariableToSchemaVariable nameCorrespondences =
	MapAsListFromSchemaVariableToSchemaVariable.EMPTY_MAP;


    /** is called by the execPostOrder-method of a term 
     * @param Term if the toplevel operator of this term is a
     * substitution of schema variables, then this pair is added to
     * the map "nameCorrespondences"
     */  
    public void visit ( Term t ) {	

	final Operator top = t.op ();
    
	if ( top instanceof SubstOp ) {
            final Operator substTermOp = t.sub ( 0 ).op ();
            final QuantifiableVariable substVar = t.varsBoundHere ( 1 ).getQuantifiableVariable ( 0 );
            if ( substTermOp instanceof SchemaVariable
                 && substVar instanceof SchemaVariable )
            addNameCorrespondence ( (SchemaVariable)substTermOp,
                                    (SchemaVariable)substVar );
        }
             
    }

    
    private void addNameCorrespondence (SchemaVariable nameReceiver,
                                        SchemaVariable nameProvider) {
        nameCorrespondences = nameCorrespondences.put ( nameReceiver,
                                                        nameProvider );
    }


    /**
     * @return the found correspondences as a map, mapping schema variable a
     *         onto schema variables b if b is replaced with a somewhere in this
     *         taclet
     */
    public MapFromSchemaVariableToSchemaVariable getCorrespondences () {
	return nameCorrespondences;
    }
   
    
    /** collects all correspondences in a semisequent 
     * @param semiseq the Semisequent to visit
     */
    private void visit(Semisequent semiseq) {
	IteratorOfConstrainedFormula it=semiseq.iterator();
	while(it.hasNext()) {
	    it.next().formula().execPostOrder(this);
	}
    }

    /** collects all correspondences in a sequent
     * @param seq the Sequent to visit
     */
    public void visit(Sequent seq) {
	visit(seq.antecedent());
	visit(seq.succedent());
    }

    /** collects all correspondences in a taclet
     * @param taclet the Taclet where the correspondences have to be
     * collected
     * @param visitAddRules a boolean that contols if the addrule sections are
     * to be ignored (iff false) or if the visitor descends into them (iff true) 
     */
    public void visit(Taclet taclet, boolean visitAddrules) {
        SchemaVariable findSV = null;
	visit(taclet.ifSequent());
	if (taclet instanceof FindTaclet) {
	    final Term findTerm = ( (FindTaclet)taclet ).find ();
            findTerm.execPostOrder ( this );
            if ( findTerm.op () instanceof SchemaVariable )
                findSV = (SchemaVariable)findTerm.op ();
	}	
	IteratorOfTacletGoalTemplate it = taclet.goalTemplates().iterator();
	while (it.hasNext()) {
	    TacletGoalTemplate gt=it.next();
	    visit(gt.sequent());
	    if (gt instanceof RewriteTacletGoalTemplate) {
		final Term replaceWithTerm = ((RewriteTacletGoalTemplate)gt).replaceWith();
		replaceWithTerm.execPostOrder(this);
                if ( findSV != null
                     && replaceWithTerm.op () instanceof SchemaVariable )
                    addNameCorrespondence ( (SchemaVariable)replaceWithTerm.op (),
                                            findSV );
	    } else {
		if(gt instanceof AntecSuccTacletGoalTemplate) {
		    visit(((AntecSuccTacletGoalTemplate)gt).replaceWith());
		}
	    }
	    if (visitAddrules) {
		IteratorOfTaclet addruleIt = gt.rules().iterator();
		while (addruleIt.hasNext()) {
		    visit(addruleIt.next(), true);		    
		}
	    }
	}
    }


}
