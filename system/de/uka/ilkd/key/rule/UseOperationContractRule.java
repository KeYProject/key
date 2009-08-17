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

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ContractConfigurator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.speclang.ClassInvariant;
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
        if(pio != null && pio.subTerm().op() instanceof UpdateApplication) {
            int targetPos = ((UpdateApplication)pio.subTerm().op()).targetPos();
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
        if(modality == Modality.BOX) {
            result = result.union(services.getSpecificationRepository()
                                          .getOperationContracts(pm, Modality.DIA));
        }
        
        assert getAllMetavariables(pio.topLevel().subTerm()).isEmpty() : "metavariables are disabled";
        
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
//        //collect information about sequent
//        PosInOccurrence pio = goBelowUpdates(ruleApp.posInOccurrence());
//        Modality modality = (Modality) pio.subTerm().op();
//        JavaBlock jb = pio.subTerm().javaBlock();
//        SourceElement activeStatement = getActiveStatement(jb);
//        MethodBodyStatement mbs = (MethodBodyStatement) activeStatement;
//        ProgramMethod pm = mbs.getProgramMethod(services);
//        Term actualSelf 
//            = (mbs.getDesignatedContext() instanceof Expression
//               ? services.getTypeConverter()
//                         .convertToLogicElement(mbs.getDesignatedContext())
//               : null);
//        ImmutableList<Term> actualParams = ImmutableSLList.<Term>nil();
//        ImmutableArray<Expression> args = mbs.getArguments();
//        for(int i = 0; i < args.size(); i++) {
//            actualParams = actualParams.append(
//                    services.getTypeConverter()
//                            .convertToLogicElement(args.getProgramElement(i)));
//        }
//        ProgramVariable actualResult 
//            = (ProgramVariable) mbs.getResultVariable();
//        
//        //configure contract and assumed / ensured invariants
//        ContractWithInvs cwi;
//        if(ruleApp instanceof UseOperationContractRuleApp) {
//            //the contract and invariants are already fixed 
//            //(probably because we're in the process of reading in a 
//            //proof from a file)
//            cwi = ((UseOperationContractRuleApp) ruleApp).getInstantiation();            
//        } else { 
//            cwi = configureContract(services, pm, modality, pio);
//        }
//        if(cwi == null) {
//            return null;
//        }
//        assert cwi.contract.getProgramMethod().equals(pm);
//
//        //create variables for self, parameters, result, exception, and a map 
//        //for atPre-functions
//        //register the newly created program variables
//        Namespace progVarNS = services.getNamespaces().programVariables();
//        ProgramVariable selfVar          
//            = SVF.createSelfVar(services, pm, true);
//        if(selfVar != null)
//            goal.addProgramVariable(selfVar);
//        
//        ImmutableList<ParsableVariable> paramVars 
//            = SVF.createParamVars(services, pm, true);
//        ImmutableList<ProgramVariable> paramVarsAsProgVars 
//            = ImmutableSLList.<ProgramVariable>nil();
//        for (ParsableVariable pvar : paramVars) {
//            assert pvar instanceof ProgramVariable 
//                   : pvar + " is not a ProgramVariable";
//            paramVarsAsProgVars 
//                = paramVarsAsProgVars.append((ProgramVariable)pvar);
//            goal.addProgramVariable((ProgramVariable)pvar);
//        }
//        
//        ProgramVariable resultVar = SVF.createResultVar(services, pm, true);
//        if(resultVar != null) {
//            goal.addProgramVariable(resultVar);
//        }
//        
//        ProgramVariable excVar = SVF.createExcVar(services, pm, true);
//        if(excVar != null) {
//            progVarNS.addSafely(excVar);
//        }
//        
//        Map<Operator, Function> atPreFunctions               
//            = new LinkedHashMap<Operator, Function>();
//        
//        //translate the contract and the invariants
//        FormulaWithAxioms pre = cwi.contract.getPre(selfVar, 
//                                                    paramVars, 
//                                                    services);
//        FormulaWithAxioms post = cwi.contract.getPost(selfVar, 
//                                                      paramVars, 
//                                                      resultVar, 
//                                                      excVar, 
//                                                      atPreFunctions,
//                                                      services);
//        ImmutableSet<LocationDescriptor> modifies = cwi.contract.getModifies(selfVar, 
//                                                                    paramVars, 
//                                                                    services);           
//        for (final ClassInvariant inv : cwi.assumedInvs) {
//            pre = pre.conjoin(inv.getClosedInv(services));
//        }
//
//        for (final ClassInvariant inv : cwi.ensuredInvs) {
//            post = post.conjoin(inv.getClosedInv(services));
//        }
//        
//        //add "actual parameters" (which in fact already are
//        //program variables in a method body statement) to modifier set
//        for(Term t : actualParams) {
//            ProgramVariable pv = (ProgramVariable) t.op();
//            modifies = modifies.add(new BasicLocationDescriptor(TB.var(pv)));
//        }
//        
//        //split goal into three branches
//        ImmutableList<Goal> result = goal.split(3);
//        Goal preGoal = result.tail().tail().head();
//        preGoal.setBranchLabel("Pre");
//        Goal postGoal = result.tail().head();
//        postGoal.setBranchLabel("Post");
//        Goal excPostGoal = result.head();
//        excPostGoal.setBranchLabel("Exceptional Post");
//        
//        //prepare common stuff for the three branches
//        UpdateFactory uf = new UpdateFactory(services, goal.simplifier());
//        AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
//        ImmutableSet<Metavariable> mvs = getAllMetavariables(pio.topLevel().subTerm());
//        Term[] mvTerms = new Term[mvs.size()];
//        final Iterator<Metavariable> it2 = mvs.iterator();
//        for(int i = 0; i < mvTerms.length; i++) {
//            assert it2.hasNext();
//            mvTerms[i] = TB.func(it2.next());
//        }            
//        Update anonUpdate = auf.createAnonymisingUpdate(modifies, 
//                                                        mvTerms, 
//                                                        services);
//        Update atPreUpdate = APF.createAtPreDefinitions(atPreFunctions, 
//                                                        services);
//        Update selfParamsUpdate = (selfVar == null
//                                   ? uf.skip()
//                                   : uf.elementaryUpdate(TB.var(selfVar), 
//                                                         actualSelf));
//        
//        final Iterator<Term> actualParamsIt = actualParams.iterator();
//        for (final ParsableVariable paramVar : paramVars) {
//            assert actualParamsIt.hasNext();
//            selfParamsUpdate 
//                = uf.parallel(selfParamsUpdate, 
//                              uf.elementaryUpdate(TB.var(paramVar), 
//                                                  actualParamsIt.next()));
//        }
//        Term excNullTerm = TB.equals(TB.var(excVar), TB.NULL(services));
//       
//        //create "Pre" branch
//        Term reachablePre = TB.and(new Term[]{
//                TB.inReachableState(services),
//                selfVar != null ? CATF.createCreatedAndNotNullTerm(services, TB.var(selfVar)) : TB.tt(),
//                CATF.createReachableVariableValuesTerm(services, 
//                                                       paramVarsAsProgVars)});
//        Term preTerm = uf.prepend(
//                selfParamsUpdate, 
//                TB.and(reachablePre, TB.imp(pre.getAxiomsAsFormula(), 
//                                            pre.getFormula())));
//        replaceInGoal(preTerm, preGoal, pio);
//        
//        //create "Post" branch
//        Term reachablePost = TB.and(
//                TB.inReachableState(services), 
//                CATF.createReachableVariableValueTerm(services, resultVar));
//        StatementBlock postSB = replaceStatement(jb, new StatementBlock());
//        Term postTermWithoutUpdate 
//            = TB.imp(TB.and(new Term[]{excNullTerm,
//                                       reachablePost,
//                                       post.getAxiomsAsFormula(),
//                                       post.getFormula()}),
//                     TB.prog(modality,
//                             JavaBlock.createJavaBlock(postSB), 
//                             pio.subTerm().sub(0)));
//        
//        Update resultUpdate = (actualResult == null
//                               ? uf.skip()
//                               : uf.elementaryUpdate(TB.var(actualResult), 
//                                                     TB.var(resultVar)));
//        
//        //case distinction necessary because UpdateFactory is unable  
//        //to deal with update compositions involving both normal and 
//        //anonym*ous* updates; replace by "else" case once this is fixed
//        Term postTerm;
//        if(anonUpdate.isAnonymousUpdate()) {
//            assert false;
//            postTerm = uf.prepend(resultUpdate, postTermWithoutUpdate);
////            postTerm = TB.tf().createAnonymousUpdateTerm(
////                                    AnonymousUpdate.getNewAnonymousOperator(), 
////                                    postTerm);
//        } else {
//            postTerm = uf.prepend(uf.sequential(new Update[]{selfParamsUpdate,
//                                                           atPreUpdate,
//                                                           anonUpdate,
//                                                           resultUpdate}),
//                                postTermWithoutUpdate);
//        }
//                                                        
//        replaceInGoal(postTerm, postGoal, pio);
//        
//        //create "Exceptional Post" branch
//        Term reachableExcPost = TB.and(
//                TB.inReachableState(services),
//                CATF.createCreatedAndNotNullTerm(services, TB.var(excVar)));
//        StatementBlock excPostSB 
//            = replaceStatement(jb, new StatementBlock(new Throw(excVar)));
//        Term excPostTermWithoutUpdate
//            = TB.imp(TB.and(new Term[]{reachableExcPost,
//                                       post.getAxiomsAsFormula(),
//                                       post.getFormula()}),
//                     TB.prog(modality,
//                             JavaBlock.createJavaBlock(excPostSB), 
//                             pio.subTerm().sub(0)));
//        Term excPostTerm = uf.prepend(uf.sequential(new Update[]{selfParamsUpdate,
//                                                               atPreUpdate,
//                                                               anonUpdate}),
//                                    excPostTermWithoutUpdate);
//                                                            
//        replaceInGoal(excPostTerm, excPostGoal, pio);
//        
//        //create justification
//        RuleJustificationBySpec just = new RuleJustificationBySpec(cwi);
//        ComplexRuleJustificationBySpec cjust 
//            = (ComplexRuleJustificationBySpec)
//              goal.proof().env().getJustifInfo().getJustification(this);
//        cjust.add(ruleApp, just);
//        
//        return result;
return null;	
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
