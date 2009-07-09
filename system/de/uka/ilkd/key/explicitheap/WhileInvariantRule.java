// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.explicitheap;

import java.util.ArrayList;
import java.util.Map;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.LoopInvariant;


public final class WhileInvariantRule implements BuiltInRule {
    
    public static final WhileInvariantRule INSTANCE = new WhileInvariantRule();
    
    private static final Name NAME = new Name("whileInvariant");
    private static final TermBuilder TB = TermBuilder.DF;
    private static final InvInferenceTools IIT = InvInferenceTools.INSTANCE;
    private static final AtPreFactory APF = AtPreFactory.INSTANCE;
    private static final ExplicitHeapConverter EHC 
    	= ExplicitHeapConverter.INSTANCE;
    
    private Term lastFocusTerm;
    private Instantiation lastInstantiation;
    
       
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    private WhileInvariantRule() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------      
    
    private Instantiation instantiate(Term focusTerm, Services services) {
        if(focusTerm == lastFocusTerm
            && lastInstantiation.inv 
                == services.getSpecificationRepository()
                           .getLoopInvariant(lastInstantiation.loop)) {
            return lastInstantiation;
        }
        
        //leading update?
        Update u;
        Term progPost;
        if(focusTerm.op() instanceof IUpdateOperator) {
            u   = Update.createUpdate(focusTerm);
            progPost = focusTerm.sub(((IUpdateOperator)(focusTerm.op())).targetPos());
        } else {
            u   = Update.createUpdate(new AssignmentPair[0]);
            progPost = focusTerm;
        }
        
        //focus (below update) must be box term
        if(progPost.op() != Modality.BOX) {
            return null;
        }
        
        //active statement must be while loop
        SourceElement activeStatement = IIT.getActiveStatement(progPost.javaBlock());
        if(!(activeStatement instanceof While)) {
            return null;
        }
        While loop = (While) activeStatement;
        
        //an invariant must be present for the loop
        LoopInvariant inv = services.getSpecificationRepository()
                                    .getLoopInvariant((While) activeStatement);
        if(inv == null 
            || inv.getInvariant(inv.getInternalSelfTerm(), 
                                inv.getInternalAtPreFunctions(), 
                                services) == null) {
            return null;
        }
        
        //collect self, execution context
        Term selfTerm 
            = LoopInvariantProposer.DEFAULT.getInnermostSelfTerm(progPost, 
                                                                 services);
        MethodFrame innermostMethodFrame 
                = IIT.getInnermostMethodFrame(progPost, services);
        ExecutionContext innermostExecutionContext 
            = innermostMethodFrame == null 
              ? null 
              : (ExecutionContext) innermostMethodFrame.getExecutionContext();
        
        //cache and return result
        Instantiation result = new Instantiation(u,
                                             progPost,
                                             loop,
                                             inv,
                                             selfTerm, 
                                             innermostExecutionContext);
        lastFocusTerm = focusTerm;
        lastInstantiation = result;
        return result;
    }
    
    
    private AnonymisationInfo getAnonymisation(
	    			    Update u,
                                    SetOfLocationDescriptor mod,
                                    ListOfProgramVariable relevantLocalVars,
                                    Services services,
                                    UpdateFactory uf,
                                    Goal goal) {
	final Term heapTerm = TB.heap(services);
	
	//convert modifies clause
	final Term modSet = EHC.convert(mod, services);
	
        //build anon update
        final AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);	
        Update anonUpdate = uf.skip();
        SetOfProgramVariable allowedLocalVars = SetAsListOfProgramVariable.EMPTY_SET;
        for(LocationDescriptor loc : mod) {
            if(loc instanceof BasicLocationDescriptor) {
                BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
                Term locTerm = bloc.getLocTerm();
                if(locTerm.op() instanceof ProgramVariable) {
                    assert locTerm.op() instanceof ProgramVariable;
                    Update pvAnonUpdate = auf.createAnonymisingUpdate(
                                        SetAsListOfLocationDescriptor.EMPTY_SET.add(loc), 
                                        services);
                    assert pvAnonUpdate.locationCount() == 1;
                    services.getNamespaces().functions().add(pvAnonUpdate.getAssignmentPair(0).value().op());
                    anonUpdate = uf.parallel(anonUpdate, pvAnonUpdate);
                    allowedLocalVars = allowedLocalVars.add((ProgramVariable)locTerm.op());
                }
            } 
        }
    	{                    
            String anonHeapName 
        	= APF.getNewName("anonHeap", services, new ArrayList<String>());
            Term anonHeapTerm 
        	= TB.func(new RigidFunction(new Name(anonHeapName), 
        		                    heapTerm.sort(), 
        		                    new Sort[0]));
            services.getNamespaces().functions().add(anonHeapTerm.op());            
            Term changeToAnonHeapTerm 
            	= TB.changeHeapAtLocs(services, heapTerm, modSet, anonHeapTerm);
            Update heapAnonUpdate = uf.elementaryUpdate(heapTerm, changeToAnonHeapTerm);
            anonUpdate = uf.parallel(anonUpdate, heapAnonUpdate);
        }
    
        //prepare heap frame condition, heap frame taclet, heap atPre definitions
        final Sort objectSort = services.getJavaInfo().getJavaLangObjectAsSort();
        final Sort fieldSort = services.getTypeConverter().getHeapLDT().getFieldSort();
        final LogicVariable objVar = new LogicVariable(new Name("o"), objectSort);
        final LogicVariable fieldVar = new LogicVariable(new Name("f"), fieldSort);
        final Term objVarTerm   = TB.var(objVar);
        final Term fieldVarTerm = TB.var(fieldVar);
        
        final Term heapAtPreTerm
                = TB.func(APF.createAtPreFunction(heapTerm.op(), services));
        services.getNamespaces().functions().add(heapAtPreTerm.op());
        final Function fakeModFunction 
        	= new RigidFunction(new Name("modSet"), modSet.sort(), new Sort[0]);
        final Term modSetAtPre
        	= TB.func(APF.createAtPreFunction(fakeModFunction, services));
        services.getNamespaces().functions().add(modSetAtPre.op());
        final Term heapAtPreDef = TB.and(TB.equals(heapTerm, heapAtPreTerm),
        				 TB.equals(modSet, modSetAtPre));
        final Term heapFrameCondition 
                = TB.all(new QuantifiableVariable[]{objVar, fieldVar},
                         TB.or(TB.pairElementOf(services, 
                        	                objVarTerm, 
                        	                fieldVarTerm, 
                        	                modSetAtPre),
                               TB.equals(TB.select(services,
                        	       		   Sort.ANY,
                                                   heapTerm, 
                                                   objVarTerm, 
                                                   fieldVarTerm),
                                          TB.select(services,
                                        	    Sort.ANY,
                                                    heapAtPreTerm, 
                                                    objVarTerm, 
                                                    fieldVarTerm))));
        
        //prepare local frame condition, local atPre definitions
        Term localFrameCondition = TB.tt();
        Term localAtPreDef = TB.tt();
        for(ProgramVariable pv : relevantLocalVars) {
            if(!allowedLocalVars.contains(pv)) {
                Term pvTerm = TB.var(pv);
                Term pvAtPreTerm 
                    = TB.func(APF.createAtPreFunction(pv, services));
                Term pvUnchangedTerm = TB.equals(pvTerm, pvAtPreTerm);                
                localAtPreDef 	
                    = TB.and(localAtPreDef, pvUnchangedTerm);
                localFrameCondition
                    = TB.and(localFrameCondition, pvUnchangedTerm);
            }
        }
        
        
        //put together
        final Term frameCondition = TB.and(heapFrameCondition, localFrameCondition);
        final Term atPreDef = TB.and(heapAtPreDef, localAtPreDef);
        
        return new AnonymisationInfo(anonUpdate, 
        			     frameCondition,
        			     localFrameCondition,
        			     atPreDef);
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------   
    
    public boolean isApplicable(Goal goal,                              
                                PosInOccurrence pio,
                                Constraint userConstraint) {
        //focus must be top level succedent
        if(pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }
        
        //instantiation must succeed
        Instantiation inst = instantiate(pio.subTerm(), 
                                         goal.proof().getServices());
        return inst != null;
    }
    
    
    public ListOfGoal apply(Goal goal, 
                            Services services, 
                            RuleApp ruleApp) {
        Instantiation inst 
            = instantiate(ruleApp.posInOccurrence().subTerm(), services);
        assert inst != null;
        
        //get invariant formula, modifies clause
        Map<Operator,Function> atPreFunctions 
            = inst.inv.getInternalAtPreFunctions();
        Term invTerm
            = inst.inv.getInvariant(inst.selfTerm, atPreFunctions, services);
        SetOfLocationDescriptor mod
            = inst.inv.getModifies(inst.selfTerm, atPreFunctions, services);
        
        //get anonymising update, frame condition
        UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());        
        FreePVCollector pc = new FreePVCollector(inst.loop, services);
        pc.start();        
        AnonymisationInfo anon = getAnonymisation(inst.u, mod, pc.result(), services, uf, goal);
        
        //split goal into three branches
        ListOfGoal result = goal.split(3);
        Goal initGoal = result.tail().tail().head();
        Goal bodyGoal = result.tail().head();
        Goal useGoal  = result.head();
        initGoal.setBranchLabel("Invariant Initially Valid");
        bodyGoal.setBranchLabel("Body Preserves Invariant");
        useGoal.setBranchLabel("Use Case");
        
        //prepare common stuff for the three branches
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
        KeYJavaType booleanKJT = services.getTypeConverter().getBooleanType();
        LocationVariable guardVar 
            = new LocationVariable(new ProgramElementName("b"), booleanKJT);
        VariableSpecification guardVarSpec 
            = new VariableSpecification(guardVar, 
                                        inst.loop.getGuardExpression(), 
                                        booleanKJT);
        LocalVariableDeclaration guardVarDecl 
            = new LocalVariableDeclaration(new TypeRef(booleanKJT), 
                                           guardVarSpec);
        Statement guardVarMethodFrame 
            = inst.innermostExecutionContext == null
              ? guardVarDecl
              : new MethodFrame(null, 
                                inst.innermostExecutionContext, 
                                new StatementBlock(guardVarDecl));
        JavaBlock guardJb = JavaBlock.createJavaBlock(
                                    new StatementBlock(guardVarMethodFrame));
        Term guardTrueTerm = TB.equals(TB.var(guardVar), 
                                       booleanLDT.getTrueTerm());
        Term guardFalseTerm = TB.equals(TB.var(guardVar), 
                                        booleanLDT.getFalseTerm());
        Update uAndAnonUpdate = uf.sequential(inst.u, anon.anonUpdate);
        Term invAndFrameAndWellFormedAssumption 
        	= TB.and(new Term[]{invTerm, 
        			    anon.localFrameCondition,
        			    TB.wellFormedHeap(services)});
        
        //"Invariant Initially Valid":
        //    \replacewith (==> inv );
        initGoal.changeFormula(new ConstrainedFormula(uf.prepend(inst.u, 
                                                                 invTerm)), 
                               ruleApp.posInOccurrence());
        
        //"Body Preserves Invariant":
        //    \replacewith (==>  #atPreEqs(anon1) -> #introNewAnonUpdate(#modifies, #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post) & inv -> 
        //          (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]#v1=TRUE ->
        //          #whileInvRule(\[{.. while (#e) #s ...}\]post, 
        //                                 #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post) & inv)),anon1));
        bodyGoal.addFormula(new ConstrainedFormula(uf.prepend(inst.u, 
                                                              anon.atPreDef)), 
                           true, 
                           false);
        bodyGoal.addFormula(new ConstrainedFormula(uf.prepend(uAndAnonUpdate, 
                                                              invAndFrameAndWellFormedAssumption)), 
                           true, 
                           false);
        
        WhileInvRule wir = (WhileInvRule) AbstractMetaOperator.WHILE_INV_RULE;
        SVInstantiations svInst 
            = SVInstantiations.EMPTY_SVINSTANTIATIONS
                              .replace(null, 
                                       null,
                                       inst.innermostExecutionContext,
                                       null);
        for(SchemaVariable sv : wir.neededInstantiations(inst.loop, svInst)) {
            assert sv.isProgramSV();
            svInst = svInst.add(sv, 
                                (Name)new ProgramElementName(sv.name().toString()));
        }
        Term bodyTerm = TB.tf().createTerm(wir, 
                                           new Term[]{inst.progPost, TB.and(invTerm, anon.frameCondition)}, 
                                           null, 
                                           null);
        bodyTerm = AbstractMetaOperator.WHILE_INV_RULE.calculate(bodyTerm, 
                                                                 svInst, 
                                                                 services);
        Term guardTrueBody = TB.box(guardJb, TB.imp(guardTrueTerm, bodyTerm));
        
        bodyGoal.changeFormula(new ConstrainedFormula(uf.prepend(uAndAnonUpdate, guardTrueBody)), 
                               ruleApp.posInOccurrence());
        
        //"Use Case":
        //    \replacewith (==> #introNewAnonUpdate(#modifies, inv -> 
        //                     (\[{ method-frame(#ex):{#typeof(#e)  #v1 = #e;} }\]
        //                      (#v1=FALSE -> \[{..   ...}\]post)),anon2))
        useGoal.addFormula(new ConstrainedFormula(uf.prepend(inst.u, 
                                                             anon.atPreDef)), 
                           true, 
                           false);
        useGoal.addFormula(new ConstrainedFormula(uf.prepend(uAndAnonUpdate, 
                                                             invAndFrameAndWellFormedAssumption)), 
                           true, 
                           false);
        Term restPsi = TB.box(IIT.removeActiveStatement(inst.progPost.javaBlock(), 
        						services),
                              inst.progPost.sub(0));
        Term guardFalseRestPsi = TB.box(guardJb, 
                                        TB.imp(guardFalseTerm, restPsi));
        useGoal.changeFormula(
                new ConstrainedFormula(uf.prepend(uAndAnonUpdate, 
                                       guardFalseRestPsi)), 
                ruleApp.posInOccurrence());
                
        return result;
    }
    
    
    public Name name() {
        return NAME;
    }

    
    public String displayName() {
        return toString();
    }
    
    
    public String toString() {
        return NAME.toString();
    }
    
    
    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------
    
    private static final class Instantiation {
        public final Update u;
        public final Term progPost;        
        
        public final While loop;
        public final LoopInvariant inv;        
        public final Term selfTerm;
        public final ExecutionContext innermostExecutionContext;
        
        public Instantiation(Update u,
                             Term progPost,
                             While loop,
                             LoopInvariant inv,
                             Term selfTerm, 
                             ExecutionContext innermostExecutionContext) {
            assert u != null;
            assert progPost != null;
            assert loop != null;
            assert inv != null;            
            this.u                         = u;
            this.progPost                  = progPost;
            this.loop                      = loop;            
            this.inv                       = inv;            
            this.selfTerm                  = selfTerm;
            this.innermostExecutionContext = innermostExecutionContext;
        }
    }
    
    
    private static final class AnonymisationInfo {
        public final Update anonUpdate;
        public final Term frameCondition;
        public final Term localFrameCondition;
        public final Term atPreDef;
        
        public AnonymisationInfo(Update anonUpdate, 
                                 Term frameCondition,
                                 Term localFrameCondition,
                                 Term atPreDef) {
            assert anonUpdate != null;
            assert frameCondition != null;
            assert localFrameCondition != null;
            assert atPreDef != null;
            this.anonUpdate           = anonUpdate;
            this.frameCondition       = frameCondition;
            this.localFrameCondition  = localFrameCondition;
            this.atPreDef             = atPreDef;
        }
    }
    
    
    private static final class FreePVCollector extends JavaASTVisitor {
         private ListOfProgramVariable declaredPVs
             = SLListOfProgramVariable.EMPTY_LIST;
         private ListOfProgramVariable freePVs
             = SLListOfProgramVariable.EMPTY_LIST;
         public FreePVCollector(ProgramElement root, Services services) {
             super(root, services);
         }
         protected void doDefaultAction(SourceElement node) {
             if(node instanceof ProgramVariable) {
                 ProgramVariable pv = (ProgramVariable) node;
                 if(!pv.isMember() && !declaredPVs.contains(pv)) {
                     freePVs = freePVs.prepend(pv);
                 }
             } else if(node instanceof VariableSpecification) {
                 VariableSpecification vs = (VariableSpecification) node;
                 ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
                 if(!pv.isMember()) {
                     assert !declaredPVs.contains(pv);
                     declaredPVs = declaredPVs.prepend(pv);
                     
                     //occurrence in the declaration itself does not count
                     assert freePVs.contains(pv); 
                     freePVs = freePVs.removeFirst(pv);
                 }
             }
         }
         public ListOfProgramVariable result() {
             //remove duplicates
             ListOfProgramVariable result = SLListOfProgramVariable.EMPTY_LIST;
             IteratorOfProgramVariable it = freePVs.iterator();
             while(it.hasNext()) {
                 ProgramVariable pv = it.next();
                 if(!result.contains(pv)) {
                     result = result.prepend(pv);
                 }
             }
             return result;
         }
     }    
} 
