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
import de.uka.ilkd.key.java.recoderext.MethodCallStatement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.util.InvInferenceTools;


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
    
    private ProgramMethod getProgramMethod(Services services,
	    				   MethodReference mr, 
	    				   Term programTerm) {
	MethodFrame frame 
		= IIT.getInnermostMethodFrame(programTerm, services);
	ExecutionContext ec = frame == null 
			      ? null
			      : (ExecutionContext) frame.getExecutionContext();
	KeYJavaType staticType = mr.determineStaticPrefixType(services, ec);
	ProgramMethod pm = mr.method(services, staticType, ec);
	assert pm != null;
	return pm;
    }
    
    
    /**
     * Returns the operation contracts which are applicable for the passed 
     * operation and the passed modality
     */
    private ImmutableSet<OperationContract> getApplicableContracts(
	    						  Services services, 
                                                          ProgramMethod pm, 
                                                          Modality modality) {
        ImmutableSet<OperationContract> result 
                = services.getSpecificationRepository()
                          .getOperationContracts(pm, modality);
        
        //in box modalities, diamond contracts may be applied as well
        if(modality == Modality.BOX) {
            result = result.union(services.getSpecificationRepository()
                                          .getOperationContracts(pm, 
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
                                                Modality modality) {
        if(Main.getInstance().mediator().autoMode()) {
            ImmutableSet<OperationContract> contracts
                = getApplicableContracts(services, pm, modality);
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
                                               modality,
                                               true,
                                               true,
                                               false,
                                               false);
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

            assert pe instanceof MethodBodyStatement;
        
            int i = length - 1;
            do {
                result = curPrefix.getFirstActiveChildPos().append(result);
                i--;
                if (i >= 0) {
                    curPrefix = prefix.get(i);
                }
            } while(i >= 0);       

        } else {
            assert pe instanceof MethodBodyStatement;
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
        
        //delete--->
        final Modality modality = (Modality) term.op();
        final SourceElement activeStatement 
                = IIT.getActiveStatement(term.javaBlock());
        if(!(activeStatement instanceof MethodBodyStatement)) {
            return false;
        }
        final ProgramMethod pm = ((MethodBodyStatement)activeStatement).getProgramMethod(services);
        //<----
        
//        //active statement must be method reference
//        final Modality modality = (Modality) term.op();
//        final SourceElement activeStatement 
//                = IIT.getActiveStatement(term.javaBlock());
//        if(!(activeStatement instanceof MethodReference)) {
//            return false;
//        }
// 
//        //there must be applicable contracts for the operation
//        final MethodReference mr = (MethodReference) activeStatement;
//        final ProgramMethod pm = getProgramMethod(services, mr, term);
        final ImmutableSet<OperationContract> contracts 
                = getApplicableContracts(services, pm, modality);
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

    
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
        //collect information about sequent
	final PosInOccurrence pio = ruleApp.posInOccurrence();
	final Term term = IIT.goBelowUpdates(pio.subTerm());
        final Modality modality = (Modality) term.op();
        final JavaBlock jb = term.javaBlock();
        final SourceElement activeStatement = IIT.getActiveStatement(jb);
        final MethodBodyStatement mbs = (MethodBodyStatement) activeStatement;
        final ProgramMethod pm = mbs.getProgramMethod(services);
        final Term actualSelf 
            = (mbs.getDesignatedContext() instanceof Expression
               ? services.getTypeConverter()
                         .convertToLogicElement(mbs.getDesignatedContext())
               : null);
        final ImmutableArray<Expression> args = mbs.getArguments();        
        ImmutableList<Term> actualParams = ImmutableSLList.<Term>nil();
        for(int i = 0; i < args.size(); i++) {
            actualParams = actualParams.append(
                    services.getTypeConverter()
                            .convertToLogicElement(args.get(i)));
        }
        final LocationVariable actualResult 
            = (LocationVariable) mbs.getResultVariable();
        
        //configure contract and assumed / ensured invariants
        final OperationContract contract;
        if(ruleApp instanceof UseOperationContractRuleApp) {
            //the contract is already fixed 
            //(probably because we're in the process of reading in a 
            //proof from a file)
            contract = ((UseOperationContractRuleApp) ruleApp).getInstantiation();            
        } else { 
            contract = configureContract(services, pm, modality);
            if(contract == null) {
        	return null;
            }
        }
        assert contract.getProgramMethod().equals(pm);

        //create variables for self, parameters, result, exception, 
        //and atPre-heap
        //register the newly created program variables
        final LocationVariable selfVar = TB.selfVar(services, pm, true);
        if(selfVar != null) {
            goal.addProgramVariable(selfVar);
        }
        
        final ImmutableList<ProgramVariable> paramVars 
        	= TB.paramVars(services, pm, true);
        for(ProgramVariable paramVar : paramVars) {
            goal.addProgramVariable(paramVar);
        }
        
        final ProgramVariable resultVar = TB.resultVar(services, pm, true);
        if(resultVar != null) {
            goal.addProgramVariable(resultVar);
            assert actualResult != null;
        }
        
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
        
        //split goal into three branches
        ImmutableList<Goal> result = goal.split(3);
        Goal preGoal = result.tail().tail().head();
        preGoal.setBranchLabel("Pre");
        Goal postGoal = result.tail().head();
        postGoal.setBranchLabel("Post");
        Goal excPostGoal = result.head();
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
        final Term resultUpdate = (actualResult == null
                                   ? TB.skip()
                                   : TB.elementary(services, 
                                	   	   actualResult, 
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
        
        //create justification
        final RuleJustificationBySpec just 
        	= new RuleJustificationBySpec(contract);
        final ComplexRuleJustificationBySpec cjust 
            	= (ComplexRuleJustificationBySpec)
            	    goal.proof().env().getJustifInfo().getJustification(this);
        cjust.add(ruleApp, just);
        
        return result;
    }
    
    
    public Name name() {
        return NAME;
    }


    public String displayName() { 
        return NAME.toString();
    }
    
    
    public String toString() {
        return displayName();
    }
}
