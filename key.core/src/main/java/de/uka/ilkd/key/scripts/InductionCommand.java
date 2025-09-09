/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.scripts.meta.*;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.Nullable;

import java.util.List;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (9/8/25)
 */
public class InductionCommand implements ProofScriptCommand {
    public static final ScriptBlock DEFAULT_BLOCK = new ScriptBlock(
            List.of(new ScriptCommandAst("macro", Map.of(), List.of("auto"), null)),
            null);

    @Override
    public List<ProofScriptArgument> getArguments() {
        return ArgumentsLifter.inferScriptArguments(Parameters.class);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl,
                        ScriptCommandAst args, EngineState stateMap)
            throws ScriptException, InterruptedException {
        var params = stateMap.getValueInjector().inject(new Parameters(), args);

        var tb = stateMap.getProof().getServices().getTermBuilder();
        var intLdt = stateMap.getProof().getServices().getTypeConverter().getIntegerLDT();
        if ("natind".equals(args.commandName()) && params.on.sort() != intLdt.targetSort()) {
            throw new IllegalStateException("You forced natural induction on a non-integer type.");
        }

        if (params.on.sort() == intLdt.targetSort()) {
            inductionOnInts(uiControl, params, stateMap);
        } else if (false /* if bsum term*/) {
        } else {
            inductionOnUserDatatype(uiControl, params, stateMap);
        }
    }

    private void inductionOnUserDatatype(AbstractUserInterfaceControl uiControl, Parameters params, EngineState stateMap) {
        // TODO find the dynamic defined tabled. Instantitate it, run the code blocks.
        //      Taclet name is ("%s_Ind", ctx.name.getText());
    }

    private void inductionOnInts(AbstractUserInterfaceControl uiControl, Parameters params, EngineState stateMap) {
        // TODO find the Taclet. Instantitate it, run the code blocks.
    }

    @Override
    public String getName() {
        return "ind";
    }

    @Override
    public List<String> getAliases() {
        return List.of("natind");
    }

    @Override
    public String getDocumentation() {
        return "";
    }

    public static class Parameters {
        @Option("base")
        @Nullable
        ScriptBlock lessThan0;

        @Option("step")
        @Nullable
        ScriptBlock equals0;

        @Argument
        @Documentation("The variable to make the case distinction on")
        @MonotonicNonNull
        JTerm on;
    }
}
