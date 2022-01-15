package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.rule.TacletApp;

import javax.annotation.Nullable;
import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
public final class BranchingNamingFunctions {
    private static Map<String, BranchNamingFunction> functionList = new HashMap<>();

    private BranchingNamingFunctions() {
    }

    static {
        registerFunction("\\test", new AndLeftSplit());
    }

    public static void registerFunction(String name, BranchNamingFunction fn) {
        functionList.put(name, fn);
    }

    @Nullable
    public static BranchNamingFunction find(String name) {
        return functionList.get(name);
    }

    private static class AndLeftSplit implements BranchNamingFunction {
        @Override
        public String getName(Services services, SequentChangeInfo currentSequent, TacletApp tacletApp,
                              TermLabelState termLabelState) {
            return "blubb";
        }
    }
}
