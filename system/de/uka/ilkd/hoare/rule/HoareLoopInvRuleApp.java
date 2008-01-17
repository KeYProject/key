package de.uka.ilkd.hoare.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;

public class HoareLoopInvRuleApp extends BuiltInRuleApp {

    private final Term inv;
    private final Term decreases;
    private Name decreaseAtPreFuncName;
            
    public HoareLoopInvRuleApp(Term inv, Term decreases, BuiltInRule builtInRule, PosInOccurrence pio, 
            Constraint userConstraint) {
        super(builtInRule, pio, userConstraint);      
        this.inv = inv;
        this.decreases = decreases;
    }
    
    /** only for proof loading */
    public HoareLoopInvRuleApp(Term inv, Term decreases, 
            Name decreaseAtPreName, 
            BuiltInRule builtInRule, PosInOccurrence pio, 
            Constraint userConstraint) {
        this(inv, decreases, builtInRule, pio, userConstraint);
        this.decreaseAtPreFuncName = decreaseAtPreName;
    }

    public HoareLoopInvRuleApp(Term inv, BuiltInRule builtInRule, PosInOccurrence pio, 
            Constraint userConstraint) {
        this(inv, null, builtInRule, pio, userConstraint);      
    }

    public ListOfGoal execute(Goal goal, Services services) {
        if (decreases != null && decreaseAtPreFuncName == null) {
            int counter = 0;
            Name funcName = new Name("oldDecreaseValue");
            while (services.getNamespaces().lookup(funcName) != null) {
                funcName = new Name("oldDecreaseValue" + counter);
                counter ++;
            }
            decreaseAtPreFuncName = funcName;
        }
        return super.execute(goal, services);
    }
    
    public Name getDecreaseAtPreFuncName() {
        return decreaseAtPreFuncName;
    }
    
    
    public Term getInvariant() {
        return inv;
    }

    public Term getDecreases() {
        return decreases;
    }

    public String toString() {
        return "Loop invariant rule application";
    }

    
}
