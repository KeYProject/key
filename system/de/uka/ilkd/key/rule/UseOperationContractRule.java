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

import de.uka.ilkd.key.bugdetection.ContractAppInfo;
import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.gui.ContractConfigurator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.PercProfile;
import de.uka.ilkd.key.proof.init.RTSJProfile;
import de.uka.ilkd.key.proof.mgt.*;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;


/**
 * Implements the rule which inserts operation contracts for a method body
 * statement.
 */
public class UseOperationContractRule implements BuiltInRule {

    private static final Name NAME = new Name("Use Operation Contract");
    private static final TermBuilder TB = TermBuilder.DF;
    private static final SignatureVariablesFactory SVF 
        = SignatureVariablesFactory.INSTANCE;
    private static final AtPreFactory APF = AtPreFactory.INSTANCE;
    private static final CreatedAttributeTermFactory CATF 
        = CreatedAttributeTermFactory.INSTANCE;
    private static final String INIT_NAME 
	= ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER;
    
  
    public static final UseOperationContractRule INSTANCE 
                                            = new UseOperationContractRule();
    
    

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private UseOperationContractRule() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Returns a new PosInOccurrence which points to the same position as the 
     * passed one, except below updates.
     */
    private PosInOccurrence goBelowUpdates(PosInOccurrence pio) {
        if(pio != null && pio.subTerm().op() instanceof IUpdateOperator) {
            int targetPos = ((IUpdateOperator)pio.subTerm().op()).targetPos();
            return goBelowUpdates(pio.down(targetPos));
        } else {
            return pio;
        }
    }
    
    
    /**
     * Returns the active statement of the passed a java block.
     */
    private SourceElement getActiveStatement(JavaBlock jb) {
        assert jb.program() != null;
        
        SourceElement result = jb.program().getFirstElement();
        while(result instanceof ProgramPrefix
              && !(result instanceof StatementBlock 
                   && ((StatementBlock)result).isEmpty())) {
            if(result instanceof LabeledStatement) {
                result = ((LabeledStatement)result).getChildAt(1);
            } else {
                result = result.getFirstElement();
            }
        }
        return result;
    }
    
    
    /**
     * Returns all meta variables occurring in the passed term.
     */
    private ImmutableSet<Metavariable> getAllMetavariables(Term term) {
        ImmutableSet<Metavariable> result = DefaultImmutableSet.<Metavariable>nil();            
        
        if(term.op() instanceof Metavariable) {
            result = result.add((Metavariable) term.op());
        }
            
        for(int i = 0; i < term.arity(); i++) {
            result = result.union(getAllMetavariables(term.sub(i)));
        }

        return result;
    }
    
    
    /**
     * Returns the operation contracts which are applicable for the passed 
     * operation and the passed modality (at the passed PosInOccurrence).
     */
    private ImmutableSet<OperationContract> getApplicableContracts(Services services, 
                                                          ProgramMethod pm, 
                                                          Modality modality,
                                                          PosInOccurrence pio) {
        ImmutableSet<OperationContract> result 
                = services.getSpecificationRepository()
                          .getOperationContracts(pm, modality);
        
        //in box modalities, diamond contracts may be applied as well
        if(modality == Op.BOX) {
            result = result.union(services.getSpecificationRepository()
                                          .getOperationContracts(pm, Op.DIA));
        }
        
        //prevent application of contracts with "everything" modifier sets 
        //if metavariables are involved (hackish, see Bug 810)
        if(getAllMetavariables(pio.topLevel().subTerm()).size() > 0) {
            ProgramVariable dummySelfVar 
                = SVF.createSelfVar(services, pm, true);
            ImmutableList<ParsableVariable> dummyParamVars 
                = SVF.createParamVars(services, pm, true);
            for(OperationContract contract : result) {
                if(contract.getModifies(dummySelfVar, dummyParamVars, services)
                           .contains(EverythingLocationDescriptor.INSTANCE)) {
                    result = result.remove(contract);
                }
            }
        }
        
        return result;
    }
    
    
    /**
     * Chooses a contract to be applied together with invariants to be assumed 
     * and ensured. This is done either automatically or by asking the user.
     */
    private ContractWithInvs configureContract(Services services, 
                                               ProgramMethod pm,
                                               Modality modality,
                                               PosInOccurrence pio) {
        if(Main.getInstance().mediator().autoMode()) {
            ImmutableSet<OperationContract> contracts
                = getApplicableContracts(services, pm, modality, pio);
            if(contracts.size() == 0) {
                return null;
            }
            OperationContract combinedContract 
                = services.getSpecificationRepository()
                          .combineContracts(contracts);
            
            ImmutableSet<ClassInvariant> ownInvs
                = services.getSpecificationRepository()
                          .getClassInvariants(pm.getContainerType());
            
            //TODO: Allow user control over the used invariants, instead of 
            //always using ownInvs (see bug #913)
            return new ContractWithInvs(combinedContract,
                                        ownInvs, 
                                        ownInvs);
        } else {
            ContractConfigurator cc 
                    = new ContractConfigurator(Main.getInstance(),
                                               services,
                                               pm,
                                               modality,
                                               true,
                                               true,
                                               true,
                                               true);
            if(cc.wasSuccessful()) {
                return cc.getContractWithInvs();
            } else {
                return null;
            }
        }
    }
   
    
    /**
     * Replaces the term at the passed PosInOccurrence with the passed 
     * replacement in the passed goal.
     */
    private void replaceInGoal(Term replacement, Goal goal, PosInOccurrence pio) {
        final Map<Term, Term> replaceMap = new LinkedHashMap<Term, Term>();
        replaceMap.put(pio.subTerm(), replacement);
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
       
            final ImmutableArray<ProgramPrefix> prefix = curPrefix.getPrefixElements();
            final int length = prefix.size();
                
            // fail fast check      
            curPrefix = prefix.get(length-1);// length -1 >= 0 as prefix array 
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
            } while (i >= 0);       

        } else {
            assert pe instanceof MethodBodyStatement;
        }
        return result;
    }
    
    private ExecutionContext getExecutionContext(PosInOccurrence pio){
        if (pio==null) {
            return null;
        }
        
        Term t = pio.subTerm();        
        
        while (t.op() instanceof IUpdateOperator) {
            pio = pio.down(((IUpdateOperator)t.op()).targetPos());
            t = pio.subTerm();
        }

        if (!(t.op() instanceof Modality)) {
            return null;
        }

        final ProgramElement pe = t.executableJavaBlock().program();        

        if (pe == null) {
            return null;
        }

        ProgramElement activeStatement = (Statement) pe;
        ExecutionContext ec = null;
        
        if (activeStatement instanceof ProgramPrefix) {

            ProgramPrefix curPrefix = (ProgramPrefix)activeStatement;

            final ImmutableArray<ProgramPrefix> prefix = curPrefix.getPrefixElements();
            final int length = prefix.size();
            
            // fail fast check      
            curPrefix = prefix.get(length-1);// length -1 >= 0 as prefix array 
                                                          //contains curPrefix as first element

            activeStatement = curPrefix.getFirstActiveChildPos().getProgram(curPrefix);

            if (!(activeStatement instanceof MethodBodyStatement)) {
                return null;
            }
        
            int i = length - 1;
            do {
                if (ec == null && curPrefix instanceof MethodFrame) {
                    ec = (ExecutionContext)((MethodFrame)curPrefix).getExecutionContext(); 
                }
                i--;
                if (i >= 0) {
                    curPrefix = prefix.get(i);
                }
            } while (i >= 0);       

        } else if (!(activeStatement instanceof MethodBodyStatement)) {
            return null;
        } 
        return ec;
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
        Services services = goal.node().proof().getServices();
        
        //pio must be a modality term in succedent
        pio = goBelowUpdates(pio);
        if(pio == null 
           || pio.isInAntec() 
           || !(pio.subTerm().op() instanceof Modality)
           || pio.subTerm().javaBlock().program() == null) {
            return false;
        }
        
        //active statement must be method body statement (TODO: constructor calls, see bug 702)
        Modality modality = (Modality) pio.subTerm().op();
        SourceElement activeStatement 
                = getActiveStatement(pio.subTerm().javaBlock());
        if(!(activeStatement instanceof MethodBodyStatement)) {
            return false;
        }
 
        //there must be applicable contracts for the operation
        MethodBodyStatement mbs = (MethodBodyStatement) activeStatement;
        ProgramMethod pm = mbs.getProgramMethod(services);
        ImmutableSet<OperationContract> contracts 
                = getApplicableContracts(services, pm, modality, pio);
        if(contracts.size() == 0) {
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
        PosInOccurrence pio = goBelowUpdates(ruleApp.posInOccurrence());
        Modality modality = (Modality) pio.subTerm().op();
        JavaBlock jb = pio.subTerm().javaBlock();
        SourceElement activeStatement = getActiveStatement(jb);
        MethodBodyStatement mbs = (MethodBodyStatement) activeStatement;
        ProgramMethod pm = mbs.getProgramMethod(services);
        Term actualSelf 
            = (mbs.getDesignatedContext() instanceof Expression
               ? services.getTypeConverter()
                         .convertToLogicElement(mbs.getDesignatedContext())
               : null);
        ImmutableList<Term> actualParams = ImmutableSLList.<Term>nil();
        ImmutableArray<Expression> args = mbs.getArguments();
        for(int i = 0; i < args.size(); i++) {
            actualParams = actualParams.append(
                    services.getTypeConverter()
                            .convertToLogicElement(args.get(i)));
        }
        ProgramVariable actualResult 
            = (ProgramVariable) mbs.getResultVariable();
        
        //configure contract and assumed / ensured invariants
        ContractWithInvs cwi;
        if(ruleApp instanceof UseOperationContractRuleApp) {
            //the contract and invariants are already fixed 
            //(probably because we're in the process of reading in a 
            //proof from a file)
            cwi = ((UseOperationContractRuleApp) ruleApp).getInstantiation();            
        } else { 
            cwi = configureContract(services, pm, modality, pio);
        }
        if(cwi == null) {
            return null;
        }
        assert cwi.contract.getProgramMethod().equals(pm) : "Tries to apply contract for " + cwi.contract.getProgramMethod() + " to " + pm;

        //create variables for self, parameters, result, exception, and a map 
        //for atPre-functions
        //register the newly created program variables
        Namespace progVarNS = services.getNamespaces().programVariables();
        ProgramVariable selfVar          
            = SVF.createSelfVar(services, pm, true);
        if(selfVar != null) {
            goal.addProgramVariable(selfVar);
        }
        
        ImmutableList<ParsableVariable> paramVars 
            = SVF.createParamVars(services, pm, true);
        ImmutableList<ProgramVariable> paramVarsAsProgVars 
            = ImmutableSLList.<ProgramVariable>nil();
        for (ParsableVariable pvar : paramVars) {
            assert pvar instanceof ProgramVariable 
                   : pvar + " is not a ProgramVariable";
            paramVarsAsProgVars 
                = paramVarsAsProgVars.append((ProgramVariable)pvar);
            goal.addProgramVariable((ProgramVariable)pvar);
        }
        
        ProgramVariable resultVar = SVF.createResultVar(services, pm, true);
        if(resultVar != null) {
            goal.addProgramVariable(resultVar);
        }
        
        ProgramVariable excVar = SVF.createExcVar(services, pm, true);
        if(excVar != null) {
            progVarNS.addSafely(excVar);
        }
        
        Map<Operator, Function> atPreFunctions               
            = new LinkedHashMap<Operator, Function>();
        
        ExecutionContext ec = getExecutionContext(pio);
        Term mTerm=null;
	if(services.getProof().getSettings().getProfile() instanceof RTSJProfile ||
	   services.getProof().getSettings().getProfile() instanceof PercProfile){ 
	    if(mbs.getMethodReference().callerScope()){
		mTerm = services.getTypeConverter().convertToLogicElement(ec.getCallerMemoryArea(), ec);
	    }else if(mbs.getMethodReference().constructedScope()){
		mTerm = services.getTypeConverter().convertToLogicElement(ec.getConstructedMemoryArea(), ec);
	    }else if(mbs.getMethodReference().reentrantScope()){
		mTerm = TB.dot(
			       services.getTypeConverter().convertToLogicElement(ec.getRuntimeInstance(), ec),
			       services.getJavaInfo().getAttribute
			       ("memoryArea", services.getJavaInfo().getJavaLangObject()));
	    }else{
		mTerm = services.getTypeConverter().convertToLogicElement(ec.getMemoryArea(), ec);
	    }
	}
            
        //translate the contract and the invariants
        FormulaWithAxioms pre = cwi.contract.getPre(selfVar, 
                                                    paramVars, 
                                                    mTerm,
                                                    services);
        FormulaWithAxioms post = cwi.contract.getPost(selfVar, 
                                                      paramVars, 
                                                      resultVar, 
                                                      excVar,
                                                      mTerm,
                                                      atPreFunctions,
                                                      services);
        ImmutableSet<LocationDescriptor> modifies = cwi.contract.getModifies(selfVar, 
                                                                    paramVars, 
                                                                    services);
        
        if(pm.getName().equals(INIT_NAME)) {
            for (final ClassInvariant inv : cwi.assumedInvs) {
                pre = pre.conjoin(inv.getClosedInvExcludingOne(selfVar, services));
            }
        } else {
            for (final ClassInvariant inv : cwi.assumedInvs) {
                pre = pre.conjoin(inv.getClosedInv(services));
            }
        }

        for (final ClassInvariant inv : cwi.ensuredInvs) {
            post = post.conjoin(inv.getClosedInv(services));
        }
        
        //add "actual parameters" (which in fact already are
        //program variables in a method body statement) to modifier set
        for(Term t : actualParams) {
            ProgramVariable pv = (ProgramVariable) t.op();
            modifies = modifies.add(new BasicLocationDescriptor(TB.var(pv)));
        }
        
        
        //Store the node info before the node is split
        final NodeInfo ni = goal.node().getNodeInfo();

        //split goal into three branches
        ImmutableList<Goal> result = goal.split(3);
        Goal preGoal = result.tail().tail().head();
        preGoal.setBranchLabel("Pre");
        Goal postGoal = result.tail().head();
        postGoal.setBranchLabel("Post");
        Goal excPostGoal = result.head();
        excPostGoal.setBranchLabel("Exceptional Post");
        
        //prepare common stuff for the three branches
        UpdateFactory uf = new UpdateFactory(services, goal.simplifier());
        AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
        ImmutableSet<Metavariable> mvs = getAllMetavariables(pio.topLevel().subTerm());
        Term[] mvTerms = new Term[mvs.size()];
        final Iterator<Metavariable> it2 = mvs.iterator();
        for(int i = 0; i < mvTerms.length; i++) {
            assert it2.hasNext();
            mvTerms[i] = TB.func(it2.next());
        }            
        Update anonUpdate = auf.createAnonymisingUpdate(modifies, 
                                                        mvTerms, 
                                                        services);
        Update atPreUpdate = APF.createAtPreDefinitions(atPreFunctions, 
                                                        services);
        Update selfParamsUpdate = (selfVar == null
                                   ? uf.skip()
                                   : uf.elementaryUpdate(TB.var(selfVar), 
                                                         actualSelf));
        
        Term[] argTerms = new Term[paramVars.size()+(pm.isStatic() ? 0 : 1)];
        int i = 0;
        if(!pm.isStatic()){
            argTerms[i++] = TB.var(selfVar);
        }
        final Iterator<Term> actualParamsIt = actualParams.iterator();
        for (final ParsableVariable paramVar : paramVars) {
            assert actualParamsIt.hasNext();
            selfParamsUpdate 
                = uf.parallel(selfParamsUpdate, 
                              uf.elementaryUpdate(TB.var(paramVar), 
                                                  actualParamsIt.next()));
            argTerms[i++] = TB.var(paramVar);
        }
	Term mCons=null, ws=null;
	Update wsUpd=null;
	NamespaceSet nss = services.getNamespaces();
        Function add = (Function) nss.functions().lookup(new Name("add"));
	if(services.getProof().getSettings().getProfile() instanceof RTSJProfile || 
	   services.getProof().getSettings().getProfile() instanceof PercProfile){
	    mCons = TB.dot(mTerm, services.getJavaInfo().getAttribute(
				"consumed", "javax.realtime.MemoryArea"));
	    ws = TB.tf().createWorkingSpaceNonRigidTerm(pm, 
			   (Sort) nss.sorts().lookup(new Name("int")),
							argTerms);
	    nss.functions().add(ws.op());
	    wsUpd = uf.elementaryUpdate(mCons, TB.tf().createFunctionTerm(add, mCons, ws));
	}
        
        Term excNullTerm = TB.equals(TB.var(excVar), TB.NULL(services));
       
        //create "Pre" branch
        Term preF = pre.getFormula();
        Function leq = (Function) nss.functions().lookup(new Name("leq"));
        if(services.getProof().getSettings().getProfile() instanceof RTSJProfile && 
        		((RTSJProfile) services.getProof().getSettings().getProfile()).memoryConsumption()){
            Term wsPre = cwi.contract.getWorkingSpace(selfVar, paramVars, services);
            wsPre = TB.tf().createFunctionTerm(leq, TB.tf().createFunctionTerm(add, mCons, wsPre),
                    TB.dot(mTerm, services.getJavaInfo().getAttribute(
                            "size", "javax.realtime.MemoryArea")));
            preF = TB.and(wsPre, preF);
        }else if(services.getProof().getSettings().getProfile() instanceof PercProfile){
            Term wsPre = cwi.contract.getCallerWorkingSpace(selfVar, paramVars, services);
            wsPre = TB.tf().createFunctionTerm(leq, TB.tf().createFunctionTerm(add, mCons, wsPre),
                    TB.dot(mTerm, services.getJavaInfo().getAttribute(
                            "size", "javax.realtime.MemoryArea")));
            if(!pm.isStatic()){
                Term wsReent = cwi.contract.getReentrantWorkingSpace(selfVar, paramVars, services);
                Term rs = TB.dot(TB.var(selfVar), 
                        services.getJavaInfo().getAttribute(ImplicitFieldAdder.IMPLICIT_REENTRANT_SCOPE, 
                                services.getJavaInfo().getJavaLangObject()));
                Term rsCons = TB.dot(rs, services.getJavaInfo().getAttribute(
                        "consumed", "javax.realtime.MemoryArea"));
                Term wsPreReent = TB.tf().createFunctionTerm(leq, TB.tf().createFunctionTerm(add, rsCons, wsReent),
                        TB.dot(rs, services.getJavaInfo().getAttribute(
                                "size", "javax.realtime.MemoryArea")));
                wsPre = TB.and(wsPre, wsPreReent);
                Update rsUpd = uf.elementaryUpdate(rsCons, TB.tf().createFunctionTerm(add, rsCons, wsReent));
                wsUpd = uf.parallel(wsUpd, rsUpd);
            }
            preF = TB.and(wsPre, preF);
        }
        Term reachablePre = TB.and(new Term[]{
                TB.inReachableState(services),
                selfVar != null ? CATF.createCreatedAndNotNullTerm(services, TB.var(selfVar)) : TB.tt(),
                CATF.createReachableVariableValuesTerm(services, 
                                                       paramVarsAsProgVars)});
        Term preTerm = uf.prepend(
                selfParamsUpdate, 
                TB.and(reachablePre, TB.imp(pre.getAxiomsAsFormula(), 
                                            preF)));
        replaceInGoal(preTerm, preGoal, pio);
        
        //create "Post" branch
        Term reachablePost = TB.and(
                TB.inReachableState(services), 
                CATF.createReachableVariableValueTerm(services, resultVar));
        StatementBlock postSB = replaceStatement(jb, new StatementBlock());

        final Term contractPost = TB.and(new Term[]{excNullTerm,
                			reachablePost,
                			post.getAxiomsAsFormula(),
                			post.getFormula()});

        Term postTermWithoutUpdate 
            = TB.imp(contractPost,
                     TB.prog(modality,
                             JavaBlock.createJavaBlock(postSB), 
                             pio.subTerm().sub(0)));
        
        final Update resultUpdate = (actualResult == null
                               ? uf.skip()
                               : uf.elementaryUpdate(TB.var(actualResult), 
                                                     TB.var(resultVar)));
        
        //case distinction necessary because UpdateFactory is unable  
        //to deal with update compositions involving both normal and 
        //anonym*ous* updates; replace by "else" case once this is fixed
        Term postTerm;
        if(anonUpdate.isAnonymousUpdate()) {
            postTerm = uf.prepend(resultUpdate, postTermWithoutUpdate);
            postTerm = TB.tf().createAnonymousUpdateTerm(
                                    AnonymousUpdate.getNewAnonymousOperator(), 
                                    postTerm);
        } else {
            postTerm = uf.prepend(uf.sequential(new Update[]{selfParamsUpdate,
							     atPreUpdate,
							     wsUpd==null ? anonUpdate : uf.parallel(anonUpdate, wsUpd),
							     resultUpdate}),
                                postTermWithoutUpdate);
        }
    
        Term wsEq = TB.tt();
        if(services.getProof().getSettings().getProfile() instanceof RTSJProfile && 
        		((RTSJProfile) services.getProof().getSettings().getProfile()).memoryConsumption()){    
            wsEq = TB.equals(ws, cwi.contract.getWorkingSpace(selfVar, paramVars, services));
            wsEq = uf.apply(uf.sequential(new Update[]{selfParamsUpdate,
                    atPreUpdate}),wsEq);
        }else if(services.getProof().getSettings().getProfile() instanceof PercProfile){
//                Term size = TB.var(services.getJavaInfo().
//                        getAttribute(ImplicitFieldAdder.IMPLICIT_SIZE, pm.getKeYJavaType()));
//                wsEq = TB.equals(ws, size);
            wsEq = TB.equals(ws, cwi.contract.getCallerWorkingSpace(selfVar, paramVars, services));
            wsEq = uf.apply(uf.sequential(new Update[]{selfParamsUpdate,
                    atPreUpdate}),wsEq);
        }
            
        postTerm = TB.imp(wsEq, postTerm);
        
        replaceInGoal(postTerm, postGoal, pio);
        
        //create "Exceptional Post" branch
        Term reachableExcPost = TB.and(
                TB.inReachableState(services),
                CATF.createCreatedAndNotNullTerm(services, TB.var(excVar)));
        StatementBlock excPostSB 
            = replaceStatement(jb, new StatementBlock(new Throw(excVar)));
        Term excPostTermWithoutUpdate
            = TB.imp(TB.and(new Term[]{reachableExcPost,
                                       post.getAxiomsAsFormula(),
                                       post.getFormula()}),
                     TB.prog(modality,
                             JavaBlock.createJavaBlock(excPostSB), 
                             pio.subTerm().sub(0)));
        Term excPostTerm = uf.prepend(uf.sequential(new Update[]{selfParamsUpdate,
								 atPreUpdate,
								 wsUpd==null ? anonUpdate : uf.parallel(anonUpdate, wsUpd)}),
	    excPostTermWithoutUpdate);
        excPostTerm = TB.imp(wsEq, excPostTerm);
        
        replaceInGoal(excPostTerm, excPostGoal, pio);
        
        //create justification
        RuleJustificationBySpec just = new RuleJustificationBySpec(cwi);
        ComplexRuleJustificationBySpec cjust 
            = (ComplexRuleJustificationBySpec)
              goal.proof().env().getJustifInfo().getJustification(this);
        cjust.add(ruleApp, just);
        
        ////////////////////////////////////////////////////////////////
        // Store information about the contract rule application
        // for later use by the bugdetection package. 
        // author:gladisch
            ContractAppInfo cInfo = new ContractAppInfo();
            cInfo.anon = anonUpdate;
            cInfo.contractPost = contractPost;
            if(anonUpdate.isAnonymousUpdate()) {
                cInfo.prefix = resultUpdate;
            } else {
                cInfo.prefix = uf.sequential(new Update[]{selfParamsUpdate,
                                                               atPreUpdate,
                                                               resultUpdate});
            }
            ni.cInfo = cInfo;
        ////////////////////////////////////////////////////////////////
        
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
