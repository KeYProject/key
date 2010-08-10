// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.rule;

import java.util.Iterator;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.WorkingSpaceContractDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rtsj.logic.op.WorkingSpaceRigidOp;
import de.uka.ilkd.key.rtsj.rule.metaconstruct.PreValidInStateOfWS;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.speclang.*;

public class UseWorkingSpaceContractRule implements BuiltInRule {

    private final Name name = new Name("Use Working Space Contract");
    private final TermBuilder tb = TermBuilder.DF;
  
    
    /** The only instance of this rule */
    public static UseWorkingSpaceContractRule INSTANCE =
        new UseWorkingSpaceContractRule();

    protected UseWorkingSpaceContractRule() {
    }
    
    public boolean isApplicable(Goal goal, PosInOccurrence pos, 
            Constraint userConstraint) {
        final Services services = goal.node().proof().getServices();
        if (pos==null) {
            return false;
        }
        
        Term t = pos.subTerm();     
        
/*        if(t.op() instanceof IUpdateOperator){
            return ((IUpdateOperator) t.op()).target(t).op() instanceof 
            WorkingSpaceNonRigidOp;
        }*/
        
        while(t.op() instanceof IUpdateOperator){
            t = ((IUpdateOperator) t.op()).target(t);
        }
      
        return t.op() instanceof  IWorkingSpaceOp &&
        getSpecs(((IWorkingSpaceOp) t.op()).getProgramMethod(), services).size()!=0;   
    }
    
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
    
    public ImmutableSet<OperationContract> getSpecs(ProgramMethod pm, Services services){
        ImmutableSet<OperationContract> result = services.getSpecificationRepository()
                  .getOperationContracts(pm, Modality.DIA);
        return result;
    }
    
    /**
     * returns the name of this rule
     */
    public Name name() {
        return name;
    }
    
    private void openBranch(final Term newFormula, final Goal branchGoal, 
            String branchLabel, Services services, boolean antec) {
        branchGoal.node().getNodeInfo().setBranchLabel(branchLabel);
        branchGoal.addFormula(new ConstrainedFormula(newFormula), antec, true);
    }

    /**
     * returns the display name of this rule
     */
    public String displayName() { 
        return name.toString();
    }

    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
        
        Term ws = ruleApp.posInOccurrence().subTerm();
        Term wsNoUpd = goBelowUpdates(ruleApp.posInOccurrence()).subTerm();
        IWorkingSpaceOp wso = (IWorkingSpaceOp) wsNoUpd.op();
        TermFactory tf = TermFactory.DEFAULT;
        
        WorkingSpaceContractDialog dialog
            = new WorkingSpaceContractDialog("Working Space Contract chooser", 
                    Main.getInstance(), services, wsNoUpd);
        OperationContract spec = selectSpec(services, ws, dialog);
        int compare = dialog.compare();
        
        if(spec==null) return null;
    
        final ImmutableList<Goal> result = goal.split(2);            
           
	final Iterator<Goal> goalIt = result.iterator();
        
        if(!(ws.op() instanceof WorkingSpaceRigidOp) || !ws.op().isRigid(ws)) {
            Goal g = goalIt.next();
            openBranch(tf.createEqualityTerm(ws, 
                    PreValidInStateOfWS.applySeqUpdateToPreRec(
                    ws,  spec.getWorkingSpace(wso.getSelf(wsNoUpd), 
                            wso.getParameters(wsNoUpd), services), 
                    new UpdateFactory(services, new UpdateSimplifier()), services)),
                    g, "Working Space Axiom" ,services, true);
            
            g = goalIt.next();
            FormulaWithAxioms pre = spec.getPre(wso.getSelf(wsNoUpd), 
                    wso.getParameters(wsNoUpd), services);
            openBranch(PreValidInStateOfWS.applySeqUpdateToPreRec(
                    ws, tb.imp(pre.getAxiomsAsFormula(), pre.getFormula()),
                    new UpdateFactory(services, new UpdateSimplifier()), services) , 
                    g, "Pre valid in Prestate" ,services, false);          
            
        }else{
            Term preWS = ((WorkingSpaceRigidOp) ws.op()).getPre();
            Function leq = (Function) services.getNamespaces().
                functions().lookup(new Name("leq"));
            //        InnerVariableNamer ivn = new InnerVariableNamer(services); 
            FormulaWithAxioms pre = spec.getPre(wso.getSelf(wsNoUpd), 
                    wso.getParameters(wsNoUpd), services);
            Term specWS = spec.getWorkingSpace(wso.getSelf(wsNoUpd), 
                    wso.getParameters(wsNoUpd), services);
            if(compare == 1){
                Goal g = goalIt.next();            
                openBranch(anonymize(tf.createJunctorTerm(Op.AND,
                        tf.createJunctorTerm(Op.AND, tf.createEqualityTerm(     
                        specWS, ws), preWS), 
                                tb.and(pre.getAxiomsAsFormula(), pre.getFormula())), 
    				 services, g, Op.AND), 
                        g, "Working Space Axiom" ,services, true);
    	    /*            openBranch(anonymize(tf.createJunctorTerm(Op.AND,
                        tf.createJunctorTerm(
    		    Op.AND, tf.createFunctionTerm(leq, ws,      
                        spec.getWorkingSpace()), preWS), spec.getPre()), 
    				 services, g, Op.AND), 
    				 g, "Working Space Axiom" ,services, true);*/
                g = goalIt.next();
                openBranch(anonymize(
                        tf.createJunctorTerm(Op.IMP, preWS, 
                        tb.imp(pre.getAxiomsAsFormula(), pre.getFormula())), services, g, Op.IMP), 
                        g, "Pre", services, false);        
            }else if(compare ==-1){
                Goal g = goalIt.next();
                openBranch(anonymize(tf.createJunctorTerm(Op.AND,
                        tf.createJunctorTerm(Op.AND, tf.createFunctionTerm(      
                        leq, specWS, ws), preWS), tb.and(pre.getAxiomsAsFormula(), pre.getFormula())),
    				 services, g, Op.AND), 
                        g, "Working Space Axiom" ,services, true);
                
                g = goalIt.next();
                openBranch(anonymize(
                        tf.createJunctorTerm(
                        Op.IMP, tb.and(pre.getAxiomsAsFormula(), pre.getFormula()),
                        preWS), services, g, Op.IMP), 
                        g, "Pre", services, false);              
            }/*else if(((WorkingSpaceContractRuleApp) ruleApp).compare() ==0){
                Goal g = goalIt.next();
                openBranch(anonymize(tf.createJunctorTerm(Op.AND,
                        tf.createJunctorTerm(Op.AND, tf.createEqualityTerm(     
                        spec.getWorkingSpace(), ws), preWS), spec.getPre()), services, g, Op.AND), 
                        g, "Working Space Axiom" ,services, true);
                
                g = goalIt.next();
                openBranch(anonymize(                    
                        tf.createJunctorTerm(
                        Op.EQV, spec.getPre(), preWS), services, g, Op.IMP), 
                        g, "Pre", services, false);              
    		    }*/
        }
        return result;
    }
    
    private Term anonymize(Term t, Services services, Goal g, Junctor op){
        TermFactory tf = TermFactory.DEFAULT;
        Term irs = tf.createFunctionTerm((Function) services.getNamespaces().functions().
                lookup(new Name("inReachableState")));
        t = tf.createJunctorTermAndSimplify(op, irs, t);
        return tf.createAnonymousUpdateTerm(AnonymousUpdate.getNewAnonymousOperator(), t);       
    }
    
    private OperationContract selectSpec(Services services, 
            Term t, 
            WorkingSpaceContractDialog wscd) {
        
        while(t.op() instanceof IUpdateOperator){
            t = ((IUpdateOperator) t.op()).target(t);
        }
        
        ProgramMethod pm = ((IWorkingSpaceOp) t.op()).getProgramMethod();  
        wscd.setSpecifications(getSpecs(pm ,services));
        
        if(t.op() instanceof WorkingSpaceRigidOp){
            wscd.setCondition(((WorkingSpaceRigidOp) t.op()).getPre());
        }else{
            wscd.setCondition(null);
        }
        wscd.start(); 
        if (!wscd.wasSuccessful()) return null;
        return wscd.getOperationContract();
    }
    
    
}
