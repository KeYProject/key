package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public interface TacletBuilderCommand {
    /**
     *
     * @param name
     * @return
     */
    boolean isSuitableFor(String name);

    /**
     *
     * @return
     */
    ArgumentType[] getArgumentTypes();

    /**
     *
     * @param tacletBuilder
     * @param arguments
     * @param parameters
     * @param negated
     */
    void apply(TacletBuilder<?> tacletBuilder, Object[] arguments, List<String> parameters, boolean negated);
}
