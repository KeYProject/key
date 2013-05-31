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


package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.collection.DefaultImmutableMap;
import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SubstOp;

/**
 * This visitor is used to collect information about schema variable
 * pairs occurring within the same substitution operator within a
 * taclet. This information is used to choose names of metavariables
 * or skolem functions.
 */

public class SVNameCorrespondenceCollector extends DefaultVisitor {

    /**
     * This map contains (a, b) if there is a substitution {b a}
     * somewhere in the taclet
     */
    private ImmutableMap<SchemaVariable,SchemaVariable> nameCorrespondences =
	DefaultImmutableMap.<SchemaVariable,SchemaVariable>nilMap();


    /** is called by the execPostOrder-method of a term 
     * @param t the Term if the toplevel operator of this term is a
     * substitution of schema variables, then this pair is added to
     * the map "nameCorrespondences"
     */  
    public void visit ( Term t ) {	

	final Operator top = t.op ();
    
	if ( top instanceof SubstOp ) {
            final Operator substTermOp = t.sub ( 0 ).op ();
            final QuantifiableVariable substVar = t.varsBoundHere ( 1 ).get ( 0 );
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
    public ImmutableMap<SchemaVariable,SchemaVariable> getCorrespondences () {
	return nameCorrespondences;
    }
   
    
    /** collects all correspondences in a semisequent 
     * @param semiseq the Semisequent to visit
     */
    private void visit(Semisequent semiseq) {
        for (SequentFormula cf : semiseq) {
            cf.formula().execPostOrder(this);
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
     * @param visitAddrules a boolean that contols if the addrule sections are
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
        for (TacletGoalTemplate tacletGoalTemplate : taclet.goalTemplates()) {
            TacletGoalTemplate gt = tacletGoalTemplate;
            visit(gt.sequent());
            if (gt instanceof RewriteTacletGoalTemplate) {
                final Term replaceWithTerm = ((RewriteTacletGoalTemplate) gt).replaceWith();
                replaceWithTerm.execPostOrder(this);
                if (findSV != null
                        && replaceWithTerm.op() instanceof SchemaVariable)
                    addNameCorrespondence((SchemaVariable) replaceWithTerm.op(),
                            findSV);
            } else {
                if (gt instanceof AntecSuccTacletGoalTemplate) {
                    visit(((AntecSuccTacletGoalTemplate) gt).replaceWith());
                }
            }
            if (visitAddrules) {
                for (Taclet taclet1 : gt.rules()) {
                    visit(taclet1, true);
                }
            }
        }
    }


}
