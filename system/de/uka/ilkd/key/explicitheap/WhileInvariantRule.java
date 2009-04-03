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

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.ldt.BooleanLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.LoopInvariantProposer;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.LoopInvariant;


/**
 * An implementation of the classical while invariant rule (without updates). 
 */
public final class WhileInvariantRule implements BuiltInRule {
    
    public static final WhileInvariantRule INSTANCE = new WhileInvariantRule();
    
    private static final Name NAME = new Name("whileInvariant");
    private static final TermBuilder TB = TermBuilder.DF;
    private static final InvInferenceTools IIT = InvInferenceTools.INSTANCE;
    private static final AtPreFactory APF = AtPreFactory.INSTANCE;
    
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
        if(progPost.op() != Op.BOX) {
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
    
    
    private AnonymisationInfo getAnonymisation(SetOfLocationDescriptor mod,
                                               Services services,
                                               UpdateFactory uf) {
        AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
        
        //prepare quantification over locations
        LogicVariable objVar 
            = new LogicVariable(new Name("obj"), 
                                services.getJavaInfo()
                                         .getJavaLangObjectAsSort());
        LogicVariable fieldVar
            = new LogicVariable(new Name("field"),
                                services.getJavaInfo().getFieldSort());
        Term objVarTerm   = TB.func(objVar);
        Term fieldVarTerm = TB.func(fieldVar);
        
        //build anon update and allowed-change condition
        Update anonUpdate = uf.skip();
        Term allowedChangeCondition = TB.ff();
        boolean anonymiseHeap = false;
        for(LocationDescriptor loc : mod) {
            if(loc instanceof BasicLocationDescriptor) {
                BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
                Term locTerm = bloc.getLocTerm();
                if(locTerm.op() instanceof AttributeOp) {
                    anonymiseHeap = true;
                    ProgramVariable fieldPV 
                        = (ProgramVariable)((AttributeOp)locTerm.op())
                                                            .attribute();
                    Function fieldSymbol 
                        = ExplicitHeapConverter.INSTANCE
                                               .getFieldSymbol(fieldPV, 
                                                               services);
                    
                    Term allowedChangeConditionEntry
                        = TB.ex(bloc.getLocTerm().freeVars().toArray(), 
                                TB.and(new Term[]{
                                        bloc.getFormula(),
                                        TB.equals(objVarTerm, locTerm.sub(0)),
                                        TB.equals(fieldVarTerm, 
                                                  TB.func(fieldSymbol))}));
                    allowedChangeCondition = TB.or(allowedChangeCondition, 
                                                   allowedChangeConditionEntry);
                } else if(locTerm.op() instanceof ArrayOp) {
                    anonymiseHeap = true;
                    assert false; //TODO!
                } else {
                    assert locTerm.arity() == 0;
                    Update u = auf.createAnonymisingUpdate(
                                SetAsListOfLocationDescriptor.EMPTY_SET.add(loc), 
                                services);
                    anonUpdate = uf.parallel(anonUpdate, u);
                }
            } else {
                assert loc instanceof EverythingLocationDescriptor;
                assert false : "\"*\" modifies clauses are evil";
            }
        }
        
        
        //anonymise heap, build frame condition and heapAtPre def
        final Term frameCondition;
        final Term heapAtPreDef;
        if(anonymiseHeap) {
            //update
            Term heapTerm = TB.heap(services);
            LocationDescriptor heapLoc 
                = new BasicLocationDescriptor(TB.heap(services));
            Function[] fs 
                = AnonymisingUpdateFactory.createUninterpretedFunctions(
                            new LocationDescriptor[]{heapLoc}, 
                            services);
            Term heapPrimeTerm = TB.func(fs[0]);
            Update heapUpdate = uf.elementaryUpdate(heapTerm, heapPrimeTerm);
            anonUpdate = uf.parallel(anonUpdate, heapUpdate);
            
            //frame condition, heapAtPre def
            Term heapAtPreTerm 
                = TB.func(APF.createAtPreFunction(heapTerm.op(), services));
            heapAtPreDef = TB.equals(heapTerm, heapAtPreTerm);                        
            frameCondition = 
                TB.all(new QuantifiableVariable[]{objVar, fieldVar},
                       TB.or(allowedChangeCondition,
                             TB.equals(TB.select(services, 
                                                 heapPrimeTerm, 
                                                 objVarTerm, 
                                                 fieldVarTerm),
                                        TB.select(services, 
                                                  heapAtPreTerm, 
                                                  objVarTerm, 
                                                  fieldVarTerm))));
        } else {
            frameCondition = TB.tt();
            heapAtPreDef   = TB.tt();
        }
        
        
        return new AnonymisationInfo(anonUpdate, frameCondition, heapAtPreDef);
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
        UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());
        AnonymisationInfo anon = getAnonymisation(mod, services, uf);
        Update uAndAnonUpdate = uf.sequential(inst.u, anon.anonUpdate);
        
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
                                                              anon.heapAtPreDef)), 
                           true, 
                           true);
        bodyGoal.addFormula(new ConstrainedFormula(uf.prepend(uAndAnonUpdate, 
                                                              TB.and(invTerm, anon.frameCondition))), 
                           true, 
                           true);
        
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
                                                             anon.heapAtPreDef)), 
                           true, 
                           true);
        useGoal.addFormula(new ConstrainedFormula(uf.prepend(uAndAnonUpdate, 
                                                             TB.and(invTerm, anon.frameCondition))), 
                           true, 
                           true);
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
        public final Term heapAtPreDef;
        
        public AnonymisationInfo(Update anonUpdate, 
                                 Term frameCondition,
                                 Term heapAtPreDef) {
            assert anonUpdate != null;
            assert frameCondition != null;
            assert heapAtPreDef != null;
            this.anonUpdate     = anonUpdate;
            this.frameCondition = frameCondition;
            this.heapAtPreDef   = heapAtPreDef;
        }
    }
} 
