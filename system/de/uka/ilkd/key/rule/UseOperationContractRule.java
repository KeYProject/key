// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.gui.ContractConfigurator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.util.InvInferenceTools;
import de.uka.ilkd.key.util.Pair;


/**
 * Implements the rule which inserts operation contracts for a method body
 * statement.
 */
public final class UseOperationContractRule implements BuiltInRule {
    
    public static final UseOperationContractRule INSTANCE 
                                            = new UseOperationContractRule();    

    private static final Name NAME = new Name("Use Method Contract");
    private static final TermBuilder TB = TermBuilder.DF;
    private static final InvInferenceTools IIT 
    	= InvInferenceTools.INSTANCE;
    

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private UseOperationContractRule() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Pair<Expression,MethodOrConstructorReference> getMethodCall(
	    						JavaBlock jb,
	    				                Services services) {
	final Expression resultExpr;
        final MethodOrConstructorReference mr;
        
        final SourceElement activeStatement = IIT.getActiveStatement(jb);
        //active statement must be method reference or assignment with
        //method reference
        if(activeStatement instanceof MethodReference) {
            resultExpr = null;
            mr = (MethodReference) activeStatement;
        } else if(activeStatement instanceof New 
        	  && ((New)activeStatement).getTypeDeclarationCount() == 0) {
            resultExpr = null;
            mr = (New) activeStatement;
        } else if(activeStatement instanceof CopyAssignment) {
            final CopyAssignment ca = (CopyAssignment) activeStatement;
            final Expression lhs = ca.getExpressionAt(0);
            final Expression rhs = ca.getExpressionAt(1);
            if((rhs instanceof MethodReference 
        	|| rhs instanceof New 
        	   && ((New)rhs).getTypeDeclarationCount() == 0)
               && (lhs instanceof LocationVariable 
                   || lhs instanceof FieldReference)) {
        	resultExpr = lhs;
        	mr = (MethodOrConstructorReference) rhs;
            } else {
        	return null;
            }
        } else {
            return null;
        }

        //receiver must be simple
        final ReferencePrefix rp = mr.getReferencePrefix();
        if(rp != null 
           && ! ProgramSVSort.SIMPLEEXPRESSION.canStandFor(rp, null, services)
           && ! (rp instanceof ThisReference)
           && ! (rp instanceof SuperReference)
           && ! (rp instanceof TypeReference)) {
            return null;
        } else {
            return new Pair<Expression,MethodOrConstructorReference>(resultExpr, mr);
        }
    }
    
    
    private KeYJavaType getStaticPrefixType(MethodOrConstructorReference mr,
	                                    Services services,
	                                    ExecutionContext ec) {
	if(mr instanceof MethodReference) { 
	    return ((MethodReference)mr).determineStaticPrefixType(services, 
		                         ec);
	} else {
	    New n = (New) mr;
	    return n.getKeYJavaType(services, ec);
	}
    }
    
    
    private ProgramMethod getProgramMethod(MethodOrConstructorReference mr,
	    				   KeYJavaType staticType, 
	    				   ExecutionContext ec,
	    				   Services services) {
	ProgramMethod result;	
	if(mr instanceof MethodReference) { //from MethodCall.java
	    MethodReference methRef = (MethodReference) mr;
	    if(ec != null) {
		result = methRef.method(services, staticType, ec);
		if(result == null) {
		    // if a method is declared protected and prefix and
		    // execContext are in different packages we have to
		    // simulate visibility rules like being in prefixType
		    result = methRef.method(services, 
			    staticType, 
			    methRef.getMethodSignature(services, ec), 
			    staticType);
		}
	    } else {
		result = methRef.method(services, 
			staticType, 
			methRef.getMethodSignature(services, ec), 
			staticType);
	    }
	} else {
	    New n = (New) mr;
	    ImmutableList<KeYJavaType> sig = ImmutableSLList.<KeYJavaType>nil();
	    for(Expression e : n.getArguments()) {
		sig = sig.append(e.getKeYJavaType(services, ec));
	    }
	    result = services.getJavaInfo().getConstructor(staticType, sig);
	}
	return result;
    }
    
    
    private Term getActualSelf(MethodOrConstructorReference mr,
	    		       ProgramMethod pm,
	    		       ExecutionContext ec, 
	    		       Services services) {
	final TypeConverter tc = services.getTypeConverter();
	final ReferencePrefix rp = mr.getReferencePrefix();
	if(pm.isStatic() || pm.isConstructor()) {
	    return null;
	} else if(rp == null 
		  || rp instanceof ThisReference 
		  || rp instanceof SuperReference) {
	    return tc.findThisForSort(pm.getContainerType().getSort(), ec);
	} else if(rp instanceof FieldReference
		  && ((FieldReference) rp).referencesOwnInstanceField()) {
	    final ReferencePrefix rp2 
	    	= ((FieldReference)rp).setReferencePrefix(
	    					ec.getRuntimeInstance());
	    return tc.convertToLogicElement(rp2);
	} else {
	    return tc.convertToLogicElement(rp, ec);
	}
    }
    
    
    private ImmutableList<Term> getActualParams(MethodOrConstructorReference mr,
	    					ExecutionContext ec,
	    					Services services) {        
	ImmutableList<Term> result = ImmutableSLList.<Term>nil();
	for(Expression expr : mr.getArguments()) {
	    Term actualParam 
	    	= services.getTypeConverter().convertToLogicElement(expr, ec);
	    result = result.append(actualParam);
	}
	return result;
    }
    
       
    /**
     * Returns the operation contracts which are applicable for the passed 
     * operation and the passed modality
     */
    private ImmutableSet<OperationContract> getApplicableContracts(
	    						  Services services, 
                                                          ProgramMethod pm, 
                                                          KeYJavaType kjt,
                                                          Modality modality) {
        ImmutableSet<OperationContract> result 
                = services.getSpecificationRepository()
                          .getOperationContracts(kjt, pm, modality);
        
        //in box modalities, diamond contracts may be applied as well
        if(modality == Modality.BOX) {
            result = result.union(services.getSpecificationRepository()
                                          .getOperationContracts(kjt, 
                                        	  		 pm,
                                        	  		 Modality.DIA));
        }

        return result;
    }
    
    
    /**
     * Chooses a contract to be applied. 
     * This is done either automatically or by asking the user.
     */
    private OperationContract configureContract(Services services, 
                                                ProgramMethod pm,
                                                KeYJavaType kjt,
                                                Modality modality) {
	final ImmutableSet<OperationContract> contracts
                = getApplicableContracts(services, pm, kjt, modality);
	assert !contracts.isEmpty();
        if(Main.getInstance().mediator().autoMode()) {
            return services.getSpecificationRepository()
                           .combineOperationContracts(contracts);
        } else {
            OperationContract[] contractsArr 
            	= contracts.toArray(new OperationContract[contracts.size()]);
            ContractConfigurator cc 
                    = new ContractConfigurator(Main.getInstance(),
                                               services,
                                               contractsArr,
                                               "Contracts for " + pm.getName(),
                                               true);
            if(cc.wasSuccessful()) {
                return (OperationContract) cc.getContract();
            } else {
                return null;
            }
        }
    }
    
    
    private Term getFreePost(ProgramMethod pm,
	    		     KeYJavaType kjt,
	                     ProgramVariable selfVar, 
	                     ProgramVariable resultVar,
	                     ProgramVariable heapAtPreVar,
	                     Services services) {
        final Term reachableConstructorPost;
        if(pm.isConstructor()) {
            reachableConstructorPost
                = TB.and(new Term[]{
        	      TB.not(TB.equals(TB.var(selfVar), TB.NULL(services))),
                      OpReplacer.replace(TB.heap(services), 
        	                  	 TB.var(heapAtPreVar), 
        	                   	 TB.not(TB.created(services, 
        	                   	                   TB.var(selfVar)))),
                      TB.created(services, TB.var(selfVar)),
                      TB.exactInstance(services, 
                       	               kjt.getSort(), 
                        	       TB.var(selfVar))});            
        } else {
            reachableConstructorPost = TB.tt();
        }
        
        final Term reachableResult
        	= resultVar != null 
        	  ? TB.reachableValue(services, resultVar)
                  : TB.tt();
        	  
        return TB.and(new Term[]{TB.inReachableState(services),
        			 reachableConstructorPost, 
        			 reachableResult}); 
    }
   
    
    /**
     * Replaces the term at the passed PosInOccurrence with the passed 
     * replacement in the passed goal.
     */
    private void replaceInGoal(Term orig,
	    		       Term replacement, 
	    		       Goal goal, 
	    		       PosInOccurrence pio) {
        final Map<Term, Term> replaceMap = new LinkedHashMap<Term, Term>();
        replaceMap.put(orig, replacement);
        OpReplacer or = new OpReplacer(replaceMap);
        
        ConstrainedFormula cf = pio.constrainedFormula();
        ConstrainedFormula newCf 
            = new ConstrainedFormula(or.replace(cf.formula()), 
                                     cf.constraint());
        goal.changeFormula(newCf, pio);
    }
    
    
    private PosInProgram getPosInProgram(JavaBlock jb) {
        ProgramElement pe = jb.program();        
   
        PosInProgram result = PosInProgram.TOP;
        
        if (pe instanceof ProgramPrefix) {
            ProgramPrefix curPrefix = (ProgramPrefix)pe;
       
            final ImmutableArray<ProgramPrefix> prefix 
            	= curPrefix.getPrefixElements();
            final int length = prefix.size();
                
            //fail fast check      
            curPrefix = prefix.get(length-1);//length -1 >= 0 as prefix array 
                                             //contains curPrefix as first element

            pe = curPrefix.getFirstActiveChildPos().getProgram(curPrefix);

            assert pe instanceof CopyAssignment 
                   || pe instanceof MethodReference;
        
            int i = length - 1;
            do {
                result = curPrefix.getFirstActiveChildPos().append(result);
                i--;
                if (i >= 0) {
                    curPrefix = prefix.get(i);
                }
            } while(i >= 0);       

        } else {
            assert pe instanceof CopyAssignment 
                   || pe instanceof MethodReference;
        }
        return result;
    }
    
    
    private StatementBlock replaceStatement(JavaBlock jb, 
                                            StatementBlock replacement) {
        PosInProgram pos = getPosInProgram(jb);
        int lastPos = pos.last();
        ContextStatementBlockInstantiation csbi = 
            new ContextStatementBlockInstantiation(pos, 
                                                   pos.up().down(lastPos+1), 
                                                   null, 
                                                   jb.program());
        final NonTerminalProgramElement result = 
            ProgramContextAdder.INSTANCE.start(
                        (JavaNonTerminalProgramElement)jb.program(), 
                        replacement, 
                        csbi);
        return (StatementBlock) result;
    }

    

    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    @Override
    public boolean isApplicable(Goal goal, 
                                PosInOccurrence pio, 
                                Constraint userConstraint) {
        final Services services = goal.node().proof().getServices();
        
        //pio must be a modality term in succedent
        if(pio == null || pio.isInAntec()) {
            return false;
        }
        final Term term = IIT.goBelowUpdates(pio.subTerm());        
        if(!(term.op() instanceof Modality)
            || term.javaBlock().program() == null) {
            return false;
        }
        
        //active statement must be method call or new
        final Modality modality = (Modality) term.op();
        final Pair<Expression,MethodOrConstructorReference> methodCall
        	= getMethodCall(term.javaBlock(), goal.proof().getServices());
        if(methodCall == null) {
            return false;
        }
        
        //arguments of method call must be simple expressions
	final ExecutionContext ec 
		= IIT.getInnermostExecutionContext(term.javaBlock(), services); 
        for(Expression arg : methodCall.second.getArguments()) {
            if(!ProgramSVSort.SIMPLEEXPRESSION
        	             .canStandFor(arg, ec, services)) {
        	return false;
            }
        }
 
        //there must be applicable contracts for the operation
	final KeYJavaType staticType
		= getStaticPrefixType(methodCall.second, services, ec);
	assert staticType != null;
	final ProgramMethod pm = getProgramMethod(methodCall.second, 
		                                  staticType,
		                                  ec, 
		                                  services);
	assert pm != null;
	
        final ImmutableSet<OperationContract> contracts 
                = getApplicableContracts(services, pm, staticType, modality);
        if(contracts.isEmpty()) {
            return false;
        }
        
        //applying a contract here must not create circular dependencies 
        //between proofs
        if(!goal.proof().mgt().contractApplicableFor(staticType, pm)) {
            return false;
        }

        return true;
    }

    
    @Override    
    public ImmutableList<Goal> apply(Goal goal, 
	    			     Services services, 
	    			     RuleApp ruleApp) {
        //collect information about sequent
	final PosInOccurrence pio = ruleApp.posInOccurrence();
	final Term term = IIT.goBelowUpdates(pio.subTerm());
        final Modality modality = (Modality) term.op();
        final JavaBlock jb = term.javaBlock();
        final Pair<Expression,MethodOrConstructorReference> methodCall
        	= getMethodCall(term.javaBlock(), services);
        final ExecutionContext ec 
		= IIT.getInnermostExecutionContext(term.javaBlock(), services);
	final KeYJavaType staticType 
		= getStaticPrefixType(methodCall.second, services, ec);
	final ProgramMethod pm 
		= getProgramMethod(methodCall.second, staticType, ec, services);
	final Term actualSelf 
		= getActualSelf(methodCall.second, pm, ec, services);
	final ImmutableList<Term> actualParams
		= getActualParams(methodCall.second, ec, services);
        
        //configure contract and assumed / ensured invariants
        final OperationContract contract;
        if(ruleApp instanceof UseOperationContractRuleApp) {
            //the contract is already fixed 
            //(probably because we're in the process of reading in a 
            //proof from a file)
            contract = ((UseOperationContractRuleApp) ruleApp).getInstantiation();            
        } else { 
            contract = configureContract(services, pm, staticType, modality);
            if(contract == null) {
        	return null;
            }
        }
        assert contract.getTarget().equals(pm);

        //create variables for self, parameters, result, exception, 
        //and atPre-heap
        //register the newly created program variables
        final LocationVariable selfVar 
        	= TB.selfVar(services, pm, staticType, true);
        if(selfVar != null) {
            goal.addProgramVariable(selfVar);
        }
        assert pm.isConstructor() 
               || ((selfVar == null) == (actualSelf == null));
        
        final ImmutableList<ProgramVariable> paramVars 
        	= TB.paramVars(services, pm, true);
        for(ProgramVariable paramVar : paramVars) {
            goal.addProgramVariable(paramVar);
        }
        
        final ProgramVariable resultVar = TB.resultVar(services, pm, true);
        if(resultVar != null) {
            goal.addProgramVariable(resultVar);
        }
        assert pm.isConstructor() 
               || !(methodCall.first != null && resultVar == null);
        
        final ProgramVariable excVar = TB.excVar(services, pm, true);
        assert excVar != null;
        goal.addProgramVariable(excVar);
        
     	final LocationVariable heapAtPreVar 
     		= TB.heapAtPreVar(services, "heapBefore_" + pm.getName(), true);
     	assert heapAtPreVar != null;
     	goal.addProgramVariable(heapAtPreVar);
        final Term heapAtPre = TB.var(heapAtPreVar);
        
        //translate the contract and the invariants
        final Term pre  = contract.getPre(selfVar, paramVars, services);
        final Term post = contract.getPost(selfVar, 
        				   paramVars, 
                                           resultVar, 
                                           excVar, 
                                           heapAtPre,
                                           services);
        final Term mod = contract.getMod(selfVar, paramVars, services);
        
        //split goal into three/four branches
        final ImmutableList<Goal> result;
        final Goal preGoal, postGoal, excPostGoal, nullGoal;
        final ReferencePrefix rp = methodCall.second.getReferencePrefix();
        if(rp != null 
           && !(rp instanceof ThisReference) 
           && !(rp instanceof SuperReference)
           && !(rp instanceof TypeReference)) {
            result = goal.split(4);
            postGoal = result.tail().tail().tail().head();
            excPostGoal = result.tail().tail().head();
            preGoal = result.tail().head();
            nullGoal = result.head();
            nullGoal.setBranchLabel("Null reference (" + actualSelf + " = null)");
        } else {
            result = goal.split(3);
            postGoal = result.tail().tail().head();
            excPostGoal = result.tail().head();
            preGoal = result.head();
            nullGoal = null;
        }
        preGoal.setBranchLabel("Pre");
        postGoal.setBranchLabel("Post");
        excPostGoal.setBranchLabel("Exceptional Post");
        
        //prepare common stuff for the three branches
	final Name anonHeapName 
		= new Name(TB.newName(services, pm.getName() + "Heap"));
	final Function anonHeapFunc = new Function(anonHeapName, 
					           services.getTypeConverter()
					     	           .getHeapLDT()
					     	           .targetSort());
	services.getNamespaces().functions().addSafely(anonHeapFunc);
        final Term anonUpdate = TB.anon(services, mod, TB.func(anonHeapFunc));        	  
        final Term heapAtPreUpdate = TB.elementary(services, 
        					   heapAtPreVar, 
        					   TB.heap(services));
        
        Term selfParamsUpdate = (selfVar == null || actualSelf == null
                                 ? TB.skip()
                                 : TB.elementary(services, 
                                      	         selfVar, 
                                	       	 actualSelf));
        final Iterator<Term> actualParamsIt = actualParams.iterator();
        for(final ParsableVariable paramVar : paramVars) {
            assert actualParamsIt.hasNext();
            selfParamsUpdate 
                = TB.parallel(selfParamsUpdate, 
                              TB.elementary(services,
                        	            (LocationVariable)paramVar, 
                        	      	    actualParamsIt.next()));
        }
        final Term excNull = TB.equals(TB.var(excVar), TB.NULL(services));
        final Term excCreated = TB.created(services, TB.var(excVar));
       
        //create "Pre" branch
        replaceInGoal(term, TB.apply(selfParamsUpdate, pre), preGoal, pio);
        
        //create "Post" branch
        final Term freePost = getFreePost(pm,
	    		     		  staticType,
	    		     		  selfVar, 
	    		     		  resultVar,
	    		     		  heapAtPreVar,
	    		     		  services);
	final StatementBlock resultAssign;
	if(methodCall.first == null) {
	    resultAssign = new StatementBlock();
	} else {
	    CopyAssignment ca 
	    	= new CopyAssignment(methodCall.first, 
	    		             pm.isConstructor() ? selfVar : resultVar);
	    resultAssign = new StatementBlock(ca);
	}        
        final StatementBlock postSB 
        	= replaceStatement(jb, resultAssign);
        final Term postWithoutUpdate 
            = TB.imp(TB.and(new Term[]{excNull, freePost, post}),
                     TB.prog(modality,
                             JavaBlock.createJavaBlock(postSB),
                             term.sub(0)));        
        final Term normalPost 
        	= TB.applySequential(new Term[]{selfParamsUpdate,
                                                heapAtPreUpdate,
                                                anonUpdate},
                                     postWithoutUpdate);
        replaceInGoal(term, normalPost, postGoal, pio);
        
        //create "Exceptional Post" branch
        final Term freeExcPost = getFreePost(pm,
	    		     		     staticType,
	    		     		     selfVar, 
	    		     		     null,
	    		     		     heapAtPreVar,
	    		     		     services);
        final StatementBlock excPostSB 
            = replaceStatement(jb, new StatementBlock(new Throw(excVar)));
        final Term excPostWithoutUpdate
            = TB.imp(TB.and(new Term[]{TB.not(excNull),
        	                       excCreated, 
        	    		       freeExcPost, 
        	    		       post}),
                     TB.prog(modality,
                             JavaBlock.createJavaBlock(excPostSB), 
                             term.sub(0)));
        final Term excPost = TB.applySequential(new Term[]{selfParamsUpdate,
                                                           heapAtPreUpdate,
                                                           anonUpdate},
                                                 excPostWithoutUpdate);
        replaceInGoal(term, excPost, excPostGoal, pio);
        
        //create "Null Reference" branch
        if(nullGoal != null) {
            final Term actualSelfNotNull 
            	= TB.not(TB.equals(actualSelf, TB.NULL(services)));
            replaceInGoal(term, actualSelfNotNull, nullGoal, pio);
        }
        
        //create justification
        final RuleJustificationBySpec just 
        	= new RuleJustificationBySpec(contract);
        final ComplexRuleJustificationBySpec cjust 
            	= (ComplexRuleJustificationBySpec)
            	    goal.proof().env().getJustifInfo().getJustification(this);
        cjust.add(ruleApp, just);
        
        return result;
    }
    
    
    @Override    
    public Name name() {
        return NAME;
    }


    @Override    
    public String displayName() { 
        return NAME.toString();
    }
    

    @Override
    public String toString() {
        return displayName();
    }
}
