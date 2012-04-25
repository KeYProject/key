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

import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;


/**
 * A class axiom that connects an observer symbol representing a Java
 * method (i.e., an object of type ProgramMethod), with the corresponding
 * method body.
 */
public final class QueryAxiom extends ClassAxiom {
    
    private final String name;
    private final ProgramMethod target;    
    private final KeYJavaType kjt;        
    
    public QueryAxiom(String name, ProgramMethod target, KeYJavaType kjt) {
	assert name != null;
	assert target != null;
	assert target.getReturnType() != null;	
	assert kjt != null;
	this.name = name;
	this.target = target;	
	this.kjt = kjt;
    }
    

    @Override
    public String getName() {
	return name;
    }
    
    
    @Override
    public ObserverFunction getTarget() {
	return target;
    }    
    

    @Override
    public KeYJavaType getKJT() {
	return kjt;
    }
    
    
    @Override
    public VisibilityModifier getVisibility() {
	return new Private();
    }

    
    @Override
    public ImmutableSet<Taclet> getTaclets(
	    		ImmutableSet<Pair<Sort, ObserverFunction>> toLimit, 
	    		Services services) {
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	
	//create schema variables
	final SchemaVariable heapSV 
		= SchemaVariableFactory.createTermSV(new Name("h"), 
						     heapLDT.targetSort(), 
						     false, 
						     false);
	final SchemaVariable selfSV
		= target.isStatic()
		  ? null
	          : SchemaVariableFactory.createTermSV(new Name("self"), 
                                	               kjt.getSort(), 
                                	               false, 
                                	               false);
	final SchemaVariable[] paramSVs 
		= new SchemaVariable[target.getNumParams()];
	for(int i = 0; i < paramSVs.length; i++) {
	    paramSVs[i]
	    	= SchemaVariableFactory.createTermSV(new Name("p" + i), 
						     target.getParamType(i)
						           .getSort(), 
						     false, 
						     false);
	}
	final SchemaVariable skolemSV 
		= SchemaVariableFactory.createSkolemTermSV(
					new Name(target.getName() + "_sk"), 
					target.sort());	
	
	//create schema variables for program variables
	final ProgramSV selfProgSV
		= target.isStatic() 
		  ? null
	          : SchemaVariableFactory.createProgramSV(
	        	  	new ProgramElementName("#self"), 
				ProgramSVSort.VARIABLE, 
				false);
	final ProgramSV[] paramProgSVs = new ProgramSV[target.getNumParams()];
	for(int i = 0; i < paramProgSVs.length; i++) {	    
	    paramProgSVs[i] = SchemaVariableFactory.createProgramSV(
		    		new ProgramElementName("#p" + i), 
		    		ProgramSVSort.VARIABLE, 
		    		false);
	}
	final ProgramSV resultProgSV 
		= SchemaVariableFactory.createProgramSV(
				new ProgramElementName("#res"), 
				ProgramSVSort.VARIABLE, 
				false);
	
	//create update and postcondition linking schema variables and 
	//program variables
	Term update 
		= TB.elementary(services, heapLDT.getHeap(), TB.var(heapSV));
	update = target.isStatic() 
	         ? update 
                 : TB.parallel(update, 
                	       TB.elementary(services, 
                		       	     selfProgSV, 
                		       	     TB.var(selfSV)));
	for(int i = 0; i < paramSVs.length; i++) {
	    update = TB.parallel(update, 
		                 TB.elementary(services, 
		                	       paramProgSVs[i], 
		                	       TB.var(paramSVs[i])));
	}
	final Term post = TB.imp(TB.reachableValue(services, 
						   TB.var(resultProgSV), 
						   target.getReturnType()),
	                  	 TB.equals(TB.var(skolemSV), TB.var(resultProgSV)));
	
	//create java block
    	final ImmutableList<KeYJavaType> sig 
		= ImmutableSLList.<KeYJavaType>nil()
		                 .append(target.getParamTypes()
		                	       .toArray(
		                      new KeYJavaType[target.getNumParams()]));	
	final ProgramMethod targetImpl 
		= services.getJavaInfo().getProgramMethod(kjt, 
							  target.getName(), 
							  sig, 
							  kjt);
	final MethodBodyStatement mbs
		= new MethodBodyStatement(targetImpl,
					  selfProgSV,
					  resultProgSV,
					  new ImmutableArray<Expression>(paramProgSVs));
	final StatementBlock sb = new StatementBlock(mbs);
	final JavaBlock jb = JavaBlock.createJavaBlock(sb);
	
	//create if sequent
	final Sequent ifSeq;
	if(target.isStatic()) {
	    ifSeq = null;
	} else {
	    final Term ifFormula 
	    	= TB.exactInstance(services, kjt.getSort(), TB.var(selfSV));
	    final SequentFormula ifCf = new SequentFormula(ifFormula);
	    final Semisequent ifSemiSeq 
	    	= Semisequent.EMPTY_SEMISEQUENT.insertFirst(ifCf).semisequent();
	    ifSeq = Sequent.createAnteSequent(ifSemiSeq);
	}

	//create find
	final Term[] subs = new Term[target.arity()];	
	subs[0] = TB.var(heapSV);
	if(!target.isStatic()) {
	    subs[1] = TB.var(selfSV);
	}
	for(int i = 0; i < paramSVs.length; i++) {
	    subs[i + (target.isStatic() ? 1 : 2)] = TB.var(paramSVs[i]);	    
	}
	final Term find = TB.func(target, subs);
	
	//create replacewith
	final Term replacewith = TB.var(skolemSV);
	
	//create added sequent
	final Term addedFormula 
		= TB.apply(update, TB.prog(Modality.BOX, jb, post));
	final SequentFormula addedCf = new SequentFormula(addedFormula);
	final Semisequent addedSemiSeq = Semisequent.EMPTY_SEMISEQUENT
	                                            .insertFirst(addedCf)
	                                            .semisequent();
	final Sequent addedSeq = Sequent.createAnteSequent(addedSemiSeq);
	
	//build taclet
	final RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
	tacletBuilder.setFind(find);
	tacletBuilder.addVarsNewDependingOn(skolemSV, heapSV);
	if(!target.isStatic()) {
	    tacletBuilder.addVarsNewDependingOn(skolemSV, selfSV);
	    tacletBuilder.setIfSequent(ifSeq);
	    tacletBuilder.addVarsNew(selfProgSV, kjt.getJavaType());
	}
	for(int i = 0; i < paramSVs.length; i++) {
	    tacletBuilder.addVarsNewDependingOn(skolemSV, paramSVs[i]);
	    tacletBuilder.addVarsNew(paramProgSVs[i], 
		    		     target.getParamType(i).getJavaType());
	}
	tacletBuilder.addVarsNew(resultProgSV, 
				 target.getReturnType().getJavaType());
	tacletBuilder.setStateRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
	tacletBuilder.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(addedSeq,
					   ImmutableSLList.<Taclet>nil(),
					   replacewith));
	tacletBuilder.setName(MiscTools.toValidTacletName(name));
	tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));
	
	// return DefaultImmutableSet.<Taclet>nil(); //chrisg: Tip von Christoph Scheben (email vom 14.2.2012)
	return DefaultImmutableSet.<Taclet>nil().add(tacletBuilder.getTaclet()); 
    }    
    
    
    @Override
    public ImmutableSet<Pair<Sort, ObserverFunction>> getUsedObservers(
	    						Services services) {
	return DefaultImmutableSet.nil();
    }
    
    
    @Override
    public String toString() {
	return "query axiom for " + target;
    }
    
}
 
