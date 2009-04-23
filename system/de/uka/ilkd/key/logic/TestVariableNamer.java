// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class TestVariableNamer extends TestCase {

    private final Proof proof = new Proof(new Services());
    private final Services services = proof.getServices();
    private final ProgramVariable x     = constructProgramVariable("x");
    private final ProgramVariable xx    = constructProgramVariable("x");
    private final ProgramVariable y     = constructProgramVariable("y");
    private final ProgramVariable x_1   = constructProgramVariable("x_1");
    private final ProgramVariable x_2   = constructProgramVariable("x_2");
    private final ProgramVariable var_1 = constructProgramVariable("var_1");
    private final ProgramVariable var_2 = constructProgramVariable("var_2");
    private final ConstrainedFormula formulaWithX    = constructFormula(x);
    private final ConstrainedFormula formulaWithX_1  = constructFormula(x_1);
    private final ConstrainedFormula formulaWithVar_1= constructFormula(var_1);
    private final SortedSchemaVariable variableSV = (SortedSchemaVariable)
    	  SchemaVariableFactory.createProgramSV(new ProgramElementName("sv"),
						ProgramSVSort.VARIABLE,
						false);
    
    
    public TestVariableNamer(String name) {
	super(name);
    }
        

    private ProgramVariable constructProgramVariable(ProgramElementName name) {
	KeYJavaType myKeyJavaType
	    = new KeYJavaType(new PrimitiveSort(new Name("mysort")));
    	return new LocationVariable(name, myKeyJavaType);
    }

    private ProgramVariable constructProgramVariable(String name) {
    	ProgramElementName pen = VariableNamer.parseName(name);
	assertTrue(pen.toString().equals(name));
    	return constructProgramVariable(pen);
    }

    private ConstrainedFormula constructFormula(ProgramVariable containedVar) {
    	Statement statement = new PostIncrement(containedVar);
    	StatementBlock statementBlock = new StatementBlock(statement);
    	JavaBlock javaBlock = JavaBlock.createJavaBlock(statementBlock);

	TermFactory termFactory = TermFactory.DEFAULT;
	Term subterm = termFactory.createJunctorTerm(Op.TRUE);
	Term term = termFactory.createDiamondTerm(javaBlock, subterm);

	return new ConstrainedFormula(term);
    }

    
    private PosInOccurrence constructPIO(ConstrainedFormula formula) {
    	return new PosInOccurrence(formula, PosInTerm.TOP_LEVEL, true);
    }


    private Goal constructGoal(ConstrainedFormula containedFormula) {
    	Semisequent empty = Semisequent.EMPTY_SEMISEQUENT;
    	Semisequent ante = empty.insert(0, containedFormula).semisequent();
	Semisequent succ = empty;

    	Sequent seq = Sequent.createSequent(ante, succ);
	Node node = new Node(proof, seq);

	TacletIndex tacletIndex = new TacletIndex();
	BuiltInRuleAppIndex builtInRuleAppIndex = new BuiltInRuleAppIndex(new BuiltInRuleIndex());
	RuleAppIndex ruleAppIndex = new RuleAppIndex(tacletIndex,
						     builtInRuleAppIndex);

	return new Goal(node, ruleAppIndex);
    }


    private void addGlobal(Goal goal, ProgramVariable globalVar) {
 	SetOfProgramVariable globals = goal.getGlobalProgVars().add(globalVar);
	goal.setGlobalProgVars(globals);
    }


    private boolean inGlobals(Goal goal, ProgramVariable globalVar) {
    	IteratorOfProgramVariable it = goal.getGlobalProgVars().iterator();
	while(it.hasNext()) {
	    if(it.next() == globalVar) {
	    	return true;
	    }
	}
	return false;
    }
    
    private void addTacletApp(Goal goal, ProgramVariable containedVar) {
	Term findTerm = TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);
   	AntecTacletBuilder builder = new AntecTacletBuilder();
	builder.setFind(findTerm);
    	AntecTaclet taclet = builder.getAntecTaclet();
    	NoPosTacletApp app = NoPosTacletApp.createNoPosTacletApp(taclet);

	SchemaVariable sv
		= SchemaVariableFactory.createProgramSV(new ProgramElementName("sv"),
						        ProgramSVSort.STATEMENT,
							false);
    	Statement statement = new PostIncrement(containedVar);
	app = (NoPosTacletApp) app.addCheckedInstantiation(sv, statement, 
                goal.proof().getServices(), false);

    	goal.ruleAppIndex().tacletIndex().add(app);
    }
    
    
    private boolean inTacletApps(Goal goal, ProgramVariable containedVar) {
	RuleAppIndex ruleAppIndex = goal.ruleAppIndex();
	TacletIndex tacletIndex = ruleAppIndex.tacletIndex();
	ListOfNoPosTacletApp noPosTacletApps
		= tacletIndex.getPartialInstantiatedApps();

	IteratorOfNoPosTacletApp it = noPosTacletApps.iterator();
	while(it.hasNext()) {
	    SVInstantiations insts = it.next().instantiations();
    	    IteratorOfEntryOfSchemaVariableAndInstantiationEntry it2;
	    it2 = insts.pairIterator();
	    while(it2.hasNext()) {
	        EntryOfSchemaVariableAndInstantiationEntry e = it2.next();
		Object inst = e.value().getInstantiation();
		if(inst instanceof PostIncrement 
		   && ((PostIncrement)inst).getFirstElement() == containedVar){
		    return true;
		}
	    }
	}
	
	return false;
    }


    public void setUp() {
	UpdateSimplifier sus = new UpdateSimplifier();
	proof.setSimplifier(sus);
    }


    private void testTemporaryNames(VariableNamer vn) {
    	ProgramElementName name = vn.getTemporaryNameProposal("x");
	assertFalse(name.getProgramName().equals("x"));

	ProgramVariable v = constructProgramVariable(name);
	ConstrainedFormula formula = constructFormula(v);
	Goal goal = constructGoal(formula);
	PosInOccurrence pio = constructPIO(formula);
	v = vn.rename(v, goal, pio);
	assertTrue(v.getProgramElementName().getProgramName().equals("x"));
    }


    public void testInnerRename() {    	
    	VariableNamer vn = services.getVariableNamer();
	ProgramVariable v, w;

	PosInOccurrence pio = constructPIO(formulaWithX);
 	Goal goal = constructGoal(formulaWithX);
	Sequent originalSequent = goal.sequent();

	v = vn.rename(y, goal, pio);
	assertTrue(v.getProgramElementName().getProgramName().equals("y"));
	assertTrue(goal.sequent().equals(originalSequent));

   	v = vn.rename(xx, goal, pio);
	assertTrue(v.getProgramElementName().getProgramName().equals("x"));
	assertTrue(goal.sequent().equals(originalSequent));

	addGlobal(goal, v);
	w = vn.rename(x, goal, pio);
	assertFalse(w.getProgramElementName().getProgramName().equals("x"));
	assertFalse(goal.sequent().equals(originalSequent));
	assertTrue(inGlobals(goal, v));

	// Reset progVar namespace which was altered due to addGlobal()
	proof.getNamespaces().programVariables().reset();
	testTemporaryNames(vn);
    }


   
    
    public void testInnerRenameInTacletApps() {
     	VariableNamer vn = services.getVariableNamer();
	ProgramVariable v;
	
	PosInOccurrence pio = constructPIO(formulaWithX);
	Goal goal = constructGoal(formulaWithX);
	addGlobal(goal, xx);
	addTacletApp(goal, x);
	
	v = vn.rename(x, goal, pio);
	assertFalse(inTacletApps(goal, x));
	assertTrue(inTacletApps(goal, v));
    }
    
    public void testNameProposals() {
    	VariableNamer vn = services.getVariableNamer();
	ProgramElementName proposal;

	PosInOccurrence pio = constructPIO(formulaWithVar_1);
	Goal goal = constructGoal(formulaWithVar_1);
	
	proposal = vn.getNameProposalForSchemaVariable(null,
						       variableSV,
						       pio,
						       null,
						       null);
	assertTrue(proposal.toString().equals("var_2"));

	addGlobal(goal, var_2);

	proposal = vn.getNameProposalForSchemaVariable("var",
						       variableSV,
						       pio,
						       null,
						       null);
	assertTrue(proposal.toString().equals("var_2"));
    }
    
    
    public void testInnerRenameUniqueness() {     	
    	VariableNamer vn = services.getVariableNamer();
	ProgramVariable v;
	
	PosInOccurrence pio = constructPIO(formulaWithX_1);
	Goal goal = constructGoal(formulaWithX_1);
	addGlobal(goal, xx);
	addTacletApp(goal, x_2);
	
	v = vn.rename(x, goal, pio);
	assertTrue(v.getProgramElementName().getProgramName().equals("x_2"));
    }
    
}
