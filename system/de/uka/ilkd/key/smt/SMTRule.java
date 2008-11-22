package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.MVCollector;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfMetavariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SetAsListOfMetavariable;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.SLListOfGoal;
import de.uka.ilkd.key.proof.decproc.AbstractDecisionProcedure;
import de.uka.ilkd.key.proof.decproc.ConstraintSet;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureYices;
import de.uka.ilkd.key.proof.decproc.JavaDecisionProcedureTranslationFactory;
import de.uka.ilkd.key.proof.decproc.SimplifyException;
import de.uka.ilkd.key.proof.decproc.SimplifyTranslation;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.YicesIntegerRule;

public class SMTRule implements BuiltInRule {

        private AbstractSmtProver prover = null;
        public SMTRule(AbstractSmtProver arg1) {
                this.prover = arg1;
        }
        
        /**
         * This rule's name.
         */
        public String displayName() {
                return prover.displayName();
        }
        
        /**
         * This rule's name as Name object.
         */
        public Name name() {
                return prover.name();
        }
        
        
        public boolean isApplicable(Goal goal, PosInOccurrence pio, Constraint userConstraint) {
                boolean hasModality = false;
                
                return this.prover.isApplicable(goal, pio, userConstraint);
                
//                IteratorOfConstrainedFormula ante = goal.sequent().antecedent().iterator();
//                IteratorOfConstrainedFormula succ = goal.sequent().succedent().iterator();
                
                /*ModalityChecker mc = new ModalityChecker();
                
                for (final ConstrainedFormula currentForm : goal.sequent()) {
                        currentForm.formula().execPreOrder(mc);   
                        if (mc.hasModality()) {
                                hasModality = true;
                        }
                        mc.reset();
                }*/
                
                /*
                while (ante.hasNext()) {
                        ConstrainedFormula currentForm = ante.next();
                        Term t = currentForm.formula();
                        t.execPreOrder(mc);
                        hasModality = hasModality || mc.hasModality();
                }
                mc.reset();
                while (succ.hasNext()) {
                        ConstrainedFormula currentForm = succ.next();
                        Term t = currentForm.formula();
                        t.execPreOrder(mc);
                        hasModality = hasModality || mc.hasModality();
                }
                */
                /*
                while (!modalityFound && pioiter.hasNext()) {
                        Term t = pioiter.getSubTerm();
                        ModalityChecker v = new ModalityChecker();
                        t.execPreOrder(v);
                        modalityFound = modalityFound && v.hasModality();
                        
                        pioiter.next();
                }
                */
                //return !modalityFound;
                //return true;
        }
        
        public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {
                
                //collect all Metavariable appearing in the goal
                //                MVCollector mvc = new MVCollector();
                //                IteratorOfConstrainedFormula ante = goal.sequent().antecedent().iterator();
                //IteratorOfConstrainedFormula succ = goal.sequent().succedent().iterator();
                
//                while (ante.hasNext()) {
//                        ConstrainedFormula currentForm = ante.next();
//                        Term t = currentForm.formula();
//                        t.execPostOrder(mvc);
                //                 }
                //                
                //while (succ.hasNext()) {
                //ConstrainedFormula currentForm = succ.next();
                //      Term t = currentForm.formula();
                //      t.execPreOrder(mvc);
                //}
                
                //                IteratorOfMetavariable iom = mvc.mv();
              //  SetAsListOfMetavariable setofmv = new SetAsListOfMetavariable();
                /*try {
                        SMTTranslator trans = new SMTTranslator(goal.sequent(), new ConstraintSet(goal, null), SetAsListOfMetavariable.EMPTY_SET, services);
                        StringBuffer s = trans.translate(goal.sequent(), services);
                        System.out.println("Final Formular: " + s);
                } catch (SimplifyException e) {
                        System.out.println("!!!    Simplify Exception thrown");
                }
                return null;*/
                int valid = this.prover.isValid(goal, 30, services, ruleApp);
                if (valid == AbstractSmtProver.VALID) {
                        return SLListOfGoal.EMPTY_LIST;
                } else if (valid == AbstractSmtProver.UNKNOWN) {
                        return null;
                } else {
                        return null;
                }
        }

}
