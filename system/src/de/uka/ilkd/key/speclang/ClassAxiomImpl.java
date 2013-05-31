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


package de.uka.ilkd.key.speclang;


import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
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

    
    @Override
    public ImmutableSet<Taclet> getTaclets(
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit,
            Services services) {
        ImmutableList<ProgramVariable> replaceVars =
                ImmutableSLList.<ProgramVariable>nil();
        replaceVars = replaceVars.append(
                services.getTypeConverter().getHeapLDT().getHeap());
        if (!isStatic) {
            replaceVars = replaceVars.append(originalSelfVar);
        }
        Term rep = TB.convertToFormula(originalRep, services);
        TacletGenerator TG = TacletGenerator.getInstance();
        DefaultImmutableSet<Taclet> taclets = DefaultImmutableSet.<Taclet>nil();
        final int c = services.getCounter("classAxiom").getCountPlusPlus();
        final String namePP = "Class axiom " + c + " in " + kjt.getFullName();
        final Name tacletName = MiscTools.toValidTacletName(namePP);
        final RuleSet ruleSet = new RuleSet(new Name("classAxiom"));
        return taclets.add(TG.generateAxiomTaclet(tacletName, rep,
                                                       replaceVars, kjt, ruleSet,
                                                       services));
    }


    @Override
    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(
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
    public IObserverFunction getTarget() {
	return null;
    }

}
