/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder.branchlabel;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import javax.annotation.Nonnull;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Common definitions of {@link BranchNamingFunction}s including a register of known functions.
 *
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
public final class BranchNamingFunctions {
    private static final Logger LOGGER = LoggerFactory.getLogger(BranchNamingFunctions.class);
    private static final Map<String, Function<List<String>, BranchNamingFunction>> functionList =
        new HashMap<>();

    private BranchNamingFunctions() {}

    static {
        registerFunction("\\nameLabelOf", NameLabelOf::new);

        // for testing and debugging purpose
        registerFunction("\\test", args -> (services, currentSequent, tacletApp,
                matchConditions) -> "[" + String.join("|", args) + "]");
    }


    public static void registerFunction(String name,
            Function<List<String>, BranchNamingFunction> fn) {
        LOGGER.info("Register branch name function: {}", name);
        functionList.put(name, fn);
    }

    @Nonnull
    public static BranchNamingFunction find(String text) {
        if (!text.contains("\\")) { // Shortcut for non-dynamic branch labels
            return new SimpleStringLabel(text);
        }
        var p = new MiniLabelParser(text);
        return p.parse();
    }

    public static Function<List<String>, BranchNamingFunction> get(String branchFunctionName) {
        return functionList.get(branchFunctionName);
    }
}
