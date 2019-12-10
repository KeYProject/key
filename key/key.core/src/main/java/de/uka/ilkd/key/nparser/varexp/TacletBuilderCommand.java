package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public interface TacletBuilderCommand {
    public boolean isSuitableFor(String name);
    public ArgumentType[] getArgumentTypes();
    public void build(TacletBuilder tacletBuilder, Object[] arguments, boolean negated);
}
