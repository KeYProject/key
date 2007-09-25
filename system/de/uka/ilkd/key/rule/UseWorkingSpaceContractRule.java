package de.uka.ilkd.key.rule;

import java.util.LinkedList;

import de.uka.ilkd.key.gui.WorkingSpaceContractDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.jml.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.metaconstruct.PreValidInStateOfWS;

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
      
        return t.op() instanceof  WorkingSpaceOp &&
        getSpecs(((WorkingSpaceOp) t.op()).getProgramMethod(), services).size()!=0;   
    }
    
    public LinkedList getSpecs(ProgramMethod pm, Services services){
        Implementation2SpecMap ism = services.getImplementation2SpecMap();
        SetOfJMLMethodSpec specs = ism.getSpecsForMethod(pm); 
        KeYJavaType classType = pm.getContainerType();
        if(specs != null){
            specs = specs.union(ism.getInheritedMethodSpecs(pm, classType));
        }else{
            specs = ism.getInheritedMethodSpecs(pm, classType);
        }
        IteratorOfJMLMethodSpec mit = specs.iterator();
        LinkedList l = new LinkedList();
        while(mit.hasNext()){
            JMLMethodSpec s = mit.next();
            l.add(s);
        }
        return l;
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

    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {
        JMLMethodSpec spec = getSelectedMethodSpec(ruleApp, goal.node().proof());
        
        final ListOfGoal result = goal.split(2);            
               
        final IteratorOfGoal goalIt = result.iterator();

        Term ws = ruleApp.posInOccurrence().subTerm();
        TermFactory tf = TermFactory.DEFAULT;
        
        if(!(ws.op() instanceof WorkingSpaceOp) || !ws.op().isRigid(ws)) {
            Goal g = goalIt.next();
            openBranch(tf.createEqualityTerm(ws, 
                    PreValidInStateOfWS.applySeqUpdateToPreRec(
                    ws,  spec.getWorkingSpace(), 
                    new UpdateFactory(services, new UpdateSimplifier()))),
                    g, "Working Space Axiom" ,services, true);
            
            g = goalIt.next();
            openBranch(PreValidInStateOfWS.applySeqUpdateToPreRec(
                    ws, spec.getPre(),
                    new UpdateFactory(services, new UpdateSimplifier())) , 
                    g, "Pre valid in Prestate" ,services, false);          
            
        }else{
        
            Term preWS = ws.sub(0);
            Function leq = (Function) services.getNamespaces().
                functions().lookup(new Name("leq"));
            //        InnerVariableNamer ivn = new InnerVariableNamer(services); 
            
            if(((WorkingSpaceContractRuleApp) ruleApp).compare() ==1){
                Goal g = goalIt.next();
                openBranch(anonymize(tf.createJunctorTerm(Op.AND,
                        tf.createJunctorTerm(Op.AND, tf.createEqualityTerm(     
                        spec.getWorkingSpace(), ws), preWS), spec.getPre()), 
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
                        spec.getPre()), services, g, Op.IMP), 
                        g, "Pre", services, false);        
            }else if(((WorkingSpaceContractRuleApp) ruleApp).compare() ==-1){
                Goal g = goalIt.next();
                openBranch(anonymize(tf.createJunctorTerm(Op.AND,
                        tf.createJunctorTerm(Op.AND, tf.createFunctionTerm(      
                        leq, spec.getWorkingSpace(), ws), preWS), spec.getPre()),
    				 services, g, Op.AND), 
                        g, "Working Space Axiom" ,services, true);
                
                g = goalIt.next();
                openBranch(anonymize(
                        tf.createJunctorTerm(
                        Op.IMP, spec.getPre(), preWS), services, g, Op.IMP), 
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
    
    private JMLMethodSpec getSelectedMethodSpec(RuleApp ruleApp, Proof proof) {        
        if (ruleApp instanceof WorkingSpaceContractRuleApp) {
            return ((WorkingSpaceContractRuleApp) ruleApp).getMethodSpec();    
        }
        return null;
    }
    
    public JMLMethodSpec selectSpec(Proof proof, PosInOccurrence pos, 
            WorkingSpaceContractDialog wscd) {
        return selectSpec(proof.getServices(), proof, pos, wscd, true);
    }       
    
    private JMLMethodSpec selectSpec(Services services, 
            Proof proof, 
            PosInOccurrence pos, 
            WorkingSpaceContractDialog wscd,
            boolean allowConfiguration) {
        Term t = pos.subTerm();
        
        while(t.op() instanceof IUpdateOperator){
            t = ((IUpdateOperator) t.op()).target(t);
        }
        
        ProgramMethod pm = ((WorkingSpaceOp) t.op()).getProgramMethod();                

        wscd.setSpecifications(getSpecs(pm ,services));
        if(!(t.op() instanceof WorkingSpaceNonRigidOp)){
            wscd.setCondition(pos.subTerm().sub(0));
        }else{
            wscd.setCondition(null);
        }
        wscd.start(); 
        if (!wscd.wasSuccessful()) return null;
        return wscd.getMethodSpec();
    }
    
    
}
