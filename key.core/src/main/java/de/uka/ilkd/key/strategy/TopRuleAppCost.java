package de.uka.ilkd.key.strategy;

/**
 * Singleton implementation of the <code>RuleAppCost</code> interface, which
 * denotes a maximum cost (rule applications with this cost can't be afforded
 * at all)
 */
public class TopRuleAppCost implements RuleAppCost {

    private TopRuleAppCost () {}

    public int compareTo(RuleAppCost o) {
	if ( o instanceof TopRuleAppCost )
	    return 0;
	return 1;
    }

    public boolean equals(Object o) {
        if (o instanceof RuleAppCost) {
            return compareTo((RuleAppCost) o) == 0;
        }
        return false;
    }
    
    public int hashCode() {
        return 91879827;
    }
    
    public final RuleAppCost add (RuleAppCost cost2) {
        return INSTANCE;
    }

    public String toString () {
        return "Costs infinite";
    }

    public static final TopRuleAppCost INSTANCE = new TopRuleAppCost ();

}