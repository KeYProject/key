// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.NoFindTacletBuilder;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletBuilder;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

/**
 * Represents an axiom specified in a class.
 * @author bruns
 *
 */
public final class ClassAxiomImpl extends ClassAxiom {


    private final String name;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;
    private final Term originalRep;
    private final ProgramVariable originalSelfVar;

    /** JML axioms may not be declared static, but they may be used like static specifications.
     * This is the case when it does not refer to an instance.
     */
    private final boolean isStatic;


    public ClassAxiomImpl(String name,
	    KeYJavaType kjt,
	    VisibilityModifier visibility,
	    Term rep,
	    ProgramVariable selfVar) {
	assert name != null;
	assert kjt != null;
	assert rep.sort() == Sort.FORMULA;
	this.name = name;
	this.kjt = kjt;
	this.visibility = visibility;
	this.originalRep = rep;
	this.originalSelfVar = selfVar;
	final OpCollector oc = new OpCollector();
	originalRep.execPostOrder(oc);
	this.isStatic        = !oc.contains(originalSelfVar);
    }
    

    public ClassAxiomImpl(String name, String displayName,
        KeYJavaType kjt,
        VisibilityModifier visibility,
        Term rep,
        ProgramVariable selfVar) {
        this(name,kjt,visibility,rep,selfVar);
        this.displayName = displayName;
    }


    private Term getAxiom(ParsableVariable heapVar, 
	    ParsableVariable selfVar,
	    Services services) {
	assert heapVar != null;
	assert (selfVar != null || isStatic);
	final Map<ProgramVariable,ParsableVariable> map = new HashMap<ProgramVariable,ParsableVariable>();
	map.put(services.getTypeConverter().getHeapLDT().getHeap(), heapVar);	
	if(selfVar != null) {
	    map.put(originalSelfVar, selfVar);
	}
	final OpReplacer or = new OpReplacer(map);
	return or.replace(originalRep);
    }



    @Override
    public String getName() {
	return name;
    }



    @Override
    public KeYJavaType getKJT() {
	return kjt;
    }


    @Override
    public VisibilityModifier getVisibility() {
	return visibility;
    }

    /**
     * Returns a no-find taclet to this axiom.
     * If the axiom expression does not contain reference to self,
     * it is considered as if it were static.
     */
    public Taclet getTaclet(Services services) {
	final TacletBuilder tacletBuilder = new NoFindTacletBuilder();

	//create schema variables
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final SchemaVariable heapSV 
	= SchemaVariableFactory.createTermSV(new Name("h"), 
		heapLDT.targetSort(), 
		false, 
		false);
	final SchemaVariable selfSV = isStatic? null :
	    SchemaVariableFactory.createTermSV(new Name("self"), 
		    kjt.getSort());

	//instantiate axiom with schema variables
	final Term rawAxiom = getAxiom(heapSV, selfSV, services);
	final Pair<Term,ImmutableSet<VariableSV>> replaceBoundLVsPair 
	= replaceBoundLVsWithSVs(rawAxiom);
	final Term schemaAxiom 
	= replaceBoundLVsPair.first;
	final ImmutableSet<VariableSV> boundSVs 
	= replaceBoundLVsPair.second;

	final SequentFormula axiomSf 
	= new SequentFormula(schemaAxiom);

	//create taclet
	final Sequent addedSeq 
	= Sequent.createAnteSequent(
		Semisequent.EMPTY_SEMISEQUENT
		.insertFirst(axiomSf)
		.semisequent());	
	tacletBuilder.addTacletGoalTemplate(new AntecSuccTacletGoalTemplate(addedSeq,ImmutableSLList.<Taclet>nil(),Sequent.EMPTY_SEQUENT));

	// create a valid, unique name
	final int c = services.getCounter("classAxiom").getCountPlusPlus();
	final String namePP = "Class axiom "+c+" in "+kjt.getFullName();
	tacletBuilder.setName(MiscTools.toValidTacletName(namePP));
	tacletBuilder.addRuleSet(
		new RuleSet(new Name("classAxiom")));

	for(VariableSV boundSV : boundSVs) {
	    tacletBuilder.addVarsNotFreeIn(boundSV, heapSV);
	    if(selfSV != null) {
		tacletBuilder.addVarsNotFreeIn(boundSV, selfSV);
	    }
	}

	return tacletBuilder.getTaclet();
    }


    @Override
    public ImmutableSet<Taclet> getTaclets(
	    ImmutableSet<Pair<Sort, ObserverFunction>> toLimit,
	    Services services) {

	return DefaultImmutableSet.<Taclet>nil()
	.add(getTaclet(services));

    }


    @Override
    public ImmutableSet<Pair<Sort, ObserverFunction>> getUsedObservers(
	    Services services) {
	return DefaultImmutableSet.nil();
    }    


    @Override
    public String toString() {
	return "axiom "+originalRep.toString();
    }




    /**
     * Class axioms do not have targets (in opposition to represents clauses)
     */
    @Override
    public ObserverFunction getTarget() {
	return null;
    }
}
