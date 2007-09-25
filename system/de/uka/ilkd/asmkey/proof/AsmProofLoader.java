// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof;

import java.io.StringReader;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.asmkey.gui.ProverFrame;
import de.uka.ilkd.asmkey.parser.ast.AstProof;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.parser.TermParserFactory;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.Debug;

/**
 * This class is responsible for loading the proofs
 * of asmkey from an {@link AstProof}
 * 
 * @see AsmProofSaver
 * @author Stanislas Nanchen
 */
public class AsmProofLoader {

    private AsmProof asmProof;
    private AstProof astProof;
    private KeYMediator mediator;

    public AsmProofLoader(AsmProof proof, AstProof astProof) {
	this.astProof = astProof;
	this.asmProof = proof;
	this.mediator = ProverFrame.getInstance().mediator();
    }

     /** Load */
    public void loadProof() {
	ProofNode proofNode = ProofParser.parse(astProof.getProof());
	loadProofBranch(proofNode, asmProof.root());
    }
    
    private void loadProofBranch(ProofNode proof, Node node) {
        // rules
        List rules = proof.getRules();
        for (int i = 0; i < rules.size(); ++i) {
            if (i > 0) {
                node = node.child(0);
            }
            ProofRule rule = (ProofRule) rules.get(i);
	    if (rule instanceof ProofBuiltIn) {
		loadProofBuiltIn((ProofBuiltIn) rule, node);
	    } else {
		loadProofRule(rule, node);
	    }
        }
        // child nodes
        List children = proof.getChildren();
        for (int i = 0; i < children.size(); ++i) {
            ProofNode child = (ProofNode) children.get(i);
            loadProofBranch(child, node.child(i));
        }
    }

    private void loadProofBuiltIn(ProofBuiltIn rule, Node node) {
	Goal goal = mediator.getSelectedProof().getGoal(node);
	PosInOccurrence pos =
            PosInOccurrence.findInSequent(goal.sequent(), rule.getFormula(), rule.getPosition());

	SetOfRuleApp applics = getBuiltInRuleApp(goal, rule.getName(), pos);
	if (applics.size() != 1) {
            throw new RuntimeException(rule.getName()
                                       + ": found "
                                       + applics.size()
                                       + " applications. Don't know what to do!");
        }
	RuleApp app = applics.iterator().next();

	//SN: TO REVIEW
	mediator.applyInteractive(app, goal);
    }

    private SetOfRuleApp getBuiltInRuleApp(Goal goal, String name, PosInOccurrence pos) {	
	SetOfRuleApp result = SetAsListOfRuleApp.EMPTY_SET;
        IteratorOfRuleApp it =
	    goal.ruleAppIndex().builtInRuleAppIndex().
	    getBuiltInRule(goal,
			   pos,
			   mediator.getUserConstraint().getConstraint()).
	    iterator();

	while (it.hasNext()) {
	    RuleApp app = it.next();
	    if (app.rule().name().toString().equals(name) ){
		result = result.add(app);
	    }
	}
	
	return result;
    }

    private void loadProofRule(ProofRule rule, Node node) {
        final Goal goal = mediator.getSelectedProof().getGoal(node);        
        final Services services = goal.proof().getServices();
        
        final PosInOccurrence pos =
            PosInOccurrence.findInSequent(goal.sequent(), rule.getFormula(), rule.getPosition());
        SetOfTacletApp applics =
            mediator.getTacletApplications(goal,
                                           rule.getName(),
                                           pos);
        if (applics.size() != 1) {
            throw new RuntimeException(rule.getName()
                                       + ": found "
                                       + applics.size()
                                       + " applications. Don't know what to do!");
        }
        TacletApp app = applics.iterator().next();

        SetOfSchemaVariable vars = app.uninstantiatedVars();

	if (rule instanceof ProofTaclet) {

	    // first pass: add variables
	    for (Iterator i = ((ProofTaclet)rule).getInstantiations().iterator(); i.hasNext();) {
		ProofInstantiation inst = (ProofInstantiation) i.next();
		SchemaVariable sv = lookupName(vars, inst.getVariable());
		if (sv.isVariableSV()) {
		    LogicVariable lv = new LogicVariable(new Name(inst.getVariable()),
							 ((SortedSchemaVariable)sv).sort());
		    Term instance = TermFactory.DEFAULT.createVariableTerm(lv);
                    app = app.addCheckedInstantiation(sv, instance, services, true);
		}
	    }
	    
	    // second pass: add everything else
	    for (Iterator i = ((ProofTaclet)rule).getInstantiations().iterator(); i.hasNext();) {
		ProofInstantiation inst = (ProofInstantiation) i.next();
		SchemaVariable sv = lookupName(vars, inst.getVariable());
		if (sv.isVariableSV()) {
		    // ignore -- already done
		} else if (sv.isProgramSV()) {
		    // does not exists with ASMs
		    Debug.fail("Program schema variable should be exists in AsmKeY.");
		} else if (sv.isSkolemTermSV()) {
		    app = app.createSkolemConstant ( inst.getTerm(),
							sv,
							true, 
                                                        mediator.getServices() );
		} else {
		    Namespace varNS = mediator.var_ns();
		    varNS = goal.getVariableNamespace(varNS);
		    varNS = app.extendVarNamespaceForSV(varNS, sv);
		    String text = inst.getTerm();
		    try {
			if(sv instanceof SortedSchemaVariable) {
			    Term term = null;
			    TermParserFactory
				.createInstance().parse(new StringReader(text),
							((SortedSchemaVariable)sv).sort(),
							mediator.getServices(),
							varNS,
							mediator.func_ns(),
							mediator.sort_ns(),
							mediator.pv_ns(),
							new AbbrevMap());
			    app = app.addCheckedInstantiation((SortedSchemaVariable)sv, term, services, true);
			}else{
			    Debug.fail(sv+" should be of type SortedSchemaVariable (or?)");
			}
		    } catch (ParserException pe) {
			throw new RuntimeException("While parsing " + text + ": " + pe);
		    }
		}
	    }
	    
	    ListOfIfFormulaInstantiation ifSeqFormulaList = SLListOfIfFormulaInstantiation.EMPTY_LIST;
	    for (Iterator i = ((ProofTaclet)rule).getIfSeqFormulas().iterator(); i.hasNext();) {
		int value = ((Integer) i.next()).intValue();
		ifSeqFormulaList = ifSeqFormulaList.append(
		    new IfFormulaInstSeq(goal.sequent(), value));
	    }
	    app = app.setIfFormulaInstantiations(ifSeqFormulaList,
						 mediator.getServices(),
						 mediator.getUserConstraint().getConstraint());
	}

        app = app.createSkolemFunctions(mediator.func_ns(), mediator.getServices());

	//SN: TOREDO 
        mediator.applyInteractive(app, goal);
    }

    public static SchemaVariable lookupName(SetOfSchemaVariable vars, String id) {
	IteratorOfSchemaVariable it = vars.iterator();
	Name name = new Name(id);
	while(it.hasNext()) {
	    SchemaVariable v = it.next();
	    if (v.name().equals(name)) { return v;}
	}
	return null;
    }
}
