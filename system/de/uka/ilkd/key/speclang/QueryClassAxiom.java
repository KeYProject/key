// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.*;


public final class QueryClassAxiom implements ClassAxiom {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final String name;
    private final KeYJavaType kjt;        
    private final ProgramMethod target;
    
    public QueryClassAxiom(String name, KeYJavaType kjt, ProgramMethod target) {
	assert name != null;
	assert kjt != null;
	assert target != null;
	assert target.getKeYJavaType() != null;
	this.name = name;
	this.kjt = kjt;
	this.target = target;
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
    public ObserverFunction getTarget() {
	return target;
    }

    
    @Override
    public Term getAxiom(Services services) {
	throw new UnsupportedOperationException();
    }
    
    
    @Override
    public Taclet getAxiomAsTaclet(Services services) {
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
	          : SchemaVariableFactory.createTermSV(
	        	  	new Name(TB.shortBaseName(kjt.getSort())), 
                                kjt.getSort(), 
                                false, 
                                false);
	final SchemaVariable[] paramSVs 
		= new SchemaVariable[target.getNumParams()];
	for(int i = 0; i < paramSVs.length; i++) {
	    final Name paramName 
	        = target.getParameterDeclarationAt(i)
	                .getVariableSpecification()
	                .getProgramElementName();
	    paramSVs[i]
	    	= SchemaVariableFactory.createTermSV(paramName, 
						     target.getParamType(i)
						           .getSort(), 
						     false, 
						     false);
	}
	final SchemaVariable skolemSV 
		= SchemaVariableFactory.createSkolemTermSV(
					new Name(target.getName()), 
					target.sort());	
	
	//create program variables
	final LocationVariable selfVar 
		= TB.selfVar(services, target, kjt, false);
	assert (selfVar == null) == (target.isStatic()); 
	final LocationVariable[] paramVars 
		= TB.paramVars(services, target, false)
		    .toArray(new LocationVariable[paramSVs.length]);
	final LocationVariable resultVar = TB.resultVar(services, 
							target, 
							false);
	
	//create update and postcondition linking schema variables and 
	//program variables
	Term update 
		= TB.elementary(services, heapLDT.getHeap(), TB.var(heapSV));
	update = target.isStatic() 
	         ? update 
                 : TB.parallel(update, 
                	       TB.elementary(services, 
                		       	     selfVar, 
                		       	     TB.var(selfSV)));
	for(int i = 0; i < paramSVs.length; i++) {
	    update = TB.parallel(update, 
		                 TB.elementary(services, 
		                	       paramVars[i], 
		                	       TB.var(paramSVs[i])));
	}
	final Term post = TB.equals(TB.var(skolemSV), TB.var(resultVar));
	
	//create java block
	final MethodBodyStatement mbs
		= new MethodBodyStatement(target,
					  selfVar,
					  resultVar,
					  new ImmutableArray<Expression>(paramVars));
	final StatementBlock sb = new StatementBlock(mbs);
	final JavaBlock jb = JavaBlock.createJavaBlock(sb);
	
	//create if sequent
	final Sequent ifSeq;
	if(target.isStatic()) {
	    ifSeq = null;
	} else {
	    final Term ifFormula 
	    	= TB.exactInstance(services, kjt.getSort(), TB.var(selfSV));
	    final ConstrainedFormula ifCf = new ConstrainedFormula(ifFormula);
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
		= TB.apply(update, TB.prog(Modality.DIA, jb, post));
	final ConstrainedFormula addedCf = new ConstrainedFormula(addedFormula);
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
	}
	for(SchemaVariable sv : paramSVs) {
	    tacletBuilder.addVarsNewDependingOn(skolemSV, sv);
	}
	tacletBuilder.setStateRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
	tacletBuilder.addTacletGoalTemplate
	    (new RewriteTacletGoalTemplate(addedSeq,
					   ImmutableSLList.<Taclet>nil(),
					   replacewith));
	tacletBuilder.setName(new Name(name));
	tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));
	
	return tacletBuilder.getTaclet();
    }    
    
    
    @Override
    public String toString() {
	return "query axiom for " + target;
    }
}
