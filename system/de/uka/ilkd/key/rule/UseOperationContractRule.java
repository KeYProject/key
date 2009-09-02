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
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.MethodFrame;
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
    
    private Pair<LocationVariable,MethodReference> getMethodCall(
	    						JavaBlock jb,
	    						Services services) {
	final LocationVariable resultVar;
        final MethodReference mr;
        
        final SourceElement activeStatement = IIT.getActiveStatement(jb);
        if(activeStatement instanceof MethodReference) {
            resultVar = null;
            mr = (MethodReference) activeStatement;
        } else if(activeStatement instanceof CopyAssignment) {
            CopyAssignment ca = (CopyAssignment) activeStatement;
            Expression lhs = ca.getExpressionAt(0);
            Expression rhs = ca.getExpressionAt(1);
            if(rhs instanceof MethodReference
               && lhs instanceof LocationVariable) {
        	resultVar = (LocationVariable) lhs;
        	mr        = (MethodReference) rhs;
            } else {
        	return null;
            }
        } else {
            return null;
        }
        
        final ReferencePrefix rp = mr.getReferencePrefix();
        if(rp != null 
           && !ProgramSVSort.SIMPLEEXPRESSION.canStandFor(rp, null, services)
           && ! (rp instanceof ThisReference)
           && ! (rp instanceof SuperReference)
           && ! (rp instanceof TypeReference)) {
            return null;
        } else {
            return new Pair<LocationVariable,MethodReference>(resultVar, mr);
        }
    }
    
    
    //copied from MethodCall.java
    private ProgramMethod getProgramMethod(MethodReference mr,
	    				   KeYJavaType staticType, 
	    				   ExecutionContext ec,
	    				   Services services) {
	ProgramMethod result;
 	if(ec != null){
	    result = mr.method(services, staticType, ec);
	    if(result == null) {
		// if a method is declared protected and prefix and
		// execContext are in different packages we have to
		// simulate visibility rules like being in prefixType
		result = mr.method(services, 
				  staticType, 
				  mr.getMethodSignature(services, ec), 
				  staticType);
	    }
 	} else {
	    result = mr.method(services, 
		    	       staticType, 
		    	       mr.getMethodSignature(services, ec), 
		    	       staticType);
 	}
	return result;
    }
    
    
    private Term getActualSelf(MethodReference mr,
	    		       ProgramMethod pm,
	    		       ExecutionContext ec, 
	    		       Services services) {
	final TypeConverter tc = services.getTypeConverter();
	final ReferencePrefix rp = mr.getReferencePrefix();
	if(pm.isStatic()) {
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
    
    
    private ImmutableList<Term> getActualParams(MethodReference mr,
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
                          .getOperationContracts(pm, kjt, modality);
        
        //in box modalities, diamond contracts may be applied as well
        if(modality == Modality.BOX) {
            result = result.union(services.getSpecificationRepository()
                                          .getOperationContracts(pm, 
                                        	  		 kjt,
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
        if(Main.getInstance().mediator().autoMode()) {
            ImmutableSet<OperationContract> contracts
                = getApplicableContracts(services, pm, kjt, modality);
            if(contracts.isEmpty()) {
                return null;
            }
            return services.getSpecificationRepository()
                           .combineContracts(contracts);
        } else {
            ContractConfigurator cc 
                    = new ContractConfigurator(Main.getInstance(),
                                               services,
                                               pm,
                                               kjt,
                                               modality,
                                               true);
            if(cc.wasSuccessful()) {
                return cc.getContract();
            } else {
                return null;
            }
        }
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
        
        //active statement must be method call
        final Modality modality = (Modality) term.op();
        final Pair<LocationVariable,MethodReference> methodCall
        	= getMethodCall(term.javaBlock(), goal.proof().getServices());
        if(methodCall == null) {
            return false;
        }
	final MethodFrame frame 
		= IIT.getInnermostMethodFrame(term, services);
	final ExecutionContext ec 
		= frame == null 
                  ? null
		  : (ExecutionContext) frame.getExecutionContext();        
        
        //arguments of method call must be simple expressions
        for(Expression arg : methodCall.second.getArguments()) {
            if(!ProgramSVSort.SIMPLEEXPRESSION
        	             .canStandFor(arg, ec, services)) {
        	return false;
            }
        }
 
        //there must be applicable contracts for the operation
	final KeYJavaType staticType 
		= methodCall.second.determineStaticPrefixType(services, ec);
	final ProgramMethod pm = getProgramMethod(methodCall.second, 
		                                  staticType,
		                                  ec, 
		                                  services);
	
        final ImmutableSet<OperationContract> contracts 
                = getApplicableContracts(services, pm, staticType, modality);
        if(contracts.isEmpty()) {
            return false;
        }
        
        //applying a contract here must not create circular dependencies 
        //between proofs
        if(!goal.proof().mgt().contractApplicableFor(pm, goal)) {
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
        final Pair<LocationVariable,MethodReference> methodCall
        	= getMethodCall(term.javaBlock(), services);
	final MethodFrame frame 
		= IIT.getInnermostMethodFrame(term, services);
	final ExecutionContext ec 
		= frame == null 
                  ? null
		  : (ExecutionContext) frame.getExecutionContext();
	final KeYJavaType staticType 
		= methodCall.second.determineStaticPrefixType(services, ec);
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
        assert contract.getProgramMethod().equals(pm);

        //create variables for self, parameters, result, exception, 
        //and atPre-heap
        //register the newly created program variables
        final LocationVariable selfVar 
        	= TB.selfVar(services, pm, staticType, true);
        if(selfVar != null) {
            goal.addProgramVariable(selfVar);
        }
        assert (selfVar == null) == (actualSelf == null);
        
        final ImmutableList<ProgramVariable> paramVars 
        	= TB.paramVars(services, pm, true);
        for(ProgramVariable paramVar : paramVars) {
            goal.addProgramVariable(paramVar);
        }
        
        final ProgramVariable resultVar = TB.resultVar(services, pm, true);
        if(resultVar != null) {
            goal.addProgramVariable(resultVar);
        }
        assert !(methodCall.first != null && resultVar == null);
        
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
        final Term mod = contract.getModifies(selfVar, paramVars, services);
        
        //split goal into three/four branches
        final ImmutableList<Goal> result;
        final Goal preGoal, postGoal, excPostGoal, nullGoal;
        final ReferencePrefix rp = methodCall.second.getReferencePrefix();
        if(rp != null 
           && !(rp instanceof ThisReference) 
           && !(rp instanceof SuperReference)
           && !(rp instanceof TypeReference)) {
            result = goal.split(4);
            preGoal = result.tail().tail().tail().head();
            postGoal = result.tail().tail().head();
            excPostGoal = result.tail().head();
            nullGoal = result.head();
            nullGoal.setBranchLabel("Null reference (" + actualSelf + " = null)");
        } else {
            result = goal.split(3);
            preGoal = result.tail().tail().head();
            postGoal = result.tail().head();
            excPostGoal = result.head();
            nullGoal = null;
        }
        preGoal.setBranchLabel("Pre");
        postGoal.setBranchLabel("Post");
        excPostGoal.setBranchLabel("Exceptional Post");
        
        //prepare common stuff for the three branches
	final Name anonHeapName = new Name(TB.newName(services, "anonHeap"));
	final Function anonHeapFunc = new Function(anonHeapName, 
					           services.getTypeConverter()
					     	           .getHeapLDT()
					     	           .targetSort());
	services.getNamespaces().functions().addSafely(anonHeapFunc);
        final Term anonUpdate = TB.anon(services, mod, TB.func(anonHeapFunc));
        final Term heapAtPreUpdate = TB.elementary(services, 
        					   heapAtPreVar, 
        					   TB.heap(services));
        
        Term selfParamsUpdate = (selfVar == null
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
        final Term reachablePost = TB.and(TB.inReachableState(services), 
                		          resultVar != null
                		          ? TB.reachableValue(services, 
                		        	  	     resultVar)
                                          : TB.tt());
        final StatementBlock postSB 
        	= replaceStatement(jb, new StatementBlock());
        final Term postWithoutUpdate 
            = TB.imp(TB.and(new Term[]{excNull, reachablePost, post}),
                     TB.prog(modality,
                             JavaBlock.createJavaBlock(postSB),
                             term.sub(0)));
        final Term resultUpdate = (methodCall.first == null
                                   ? TB.skip()
                                   : TB.elementary(services, 
                                	   	   methodCall.first, 
                                	   	   TB.var(resultVar)));
        
        final Term normalPost 
        	= TB.applySequential(new Term[]{heapAtPreUpdate,
                                                selfParamsUpdate,
                                                anonUpdate,
                                                resultUpdate},
                                     postWithoutUpdate);
        replaceInGoal(term, normalPost, postGoal, pio);
        
        //create "Exceptional Post" branch
        final Term reachableExcPost = TB.inReachableState(services);
        final StatementBlock excPostSB 
            = replaceStatement(jb, new StatementBlock(new Throw(excVar)));
        final Term excPostWithoutUpdate
            = TB.imp(TB.and(new Term[]{TB.not(excNull),
        	                       excCreated, 
        	    		       reachableExcPost, 
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
