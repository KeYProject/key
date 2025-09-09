package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.scripts.meta.*;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.prover.sequent.SequentFormula;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (9/8/25)
 */
public class IntegerSplitCommand implements ProofScriptCommand {
    @Override
    public List<ProofScriptArgument> getArguments() {
        return ArgumentsLifter.inferScriptArguments(Parameters.class);
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl,
                        ScriptCommandAst args, EngineState stateMap)
            throws ScriptException, InterruptedException {
        var params = stateMap.getValueInjector().inject(new Parameters(), args);

        //checkForDatatype(params.on);
        var tb = stateMap.getProof().getServices().getTermBuilder();
        var intLdt = stateMap.getProof().getServices().getTypeConverter().getIntegerLDT();
        if (params.on.sort() != intLdt.targetSort()) {
            throw new IllegalStateException("The given term `arg0:(" + params.on + ")` should be of type " + intLdt.targetSort() + " " +
                    "but was of type: " + params.on.sort());
        }

        var goals = stateMap.getFirstOpenAutomaticGoal().split(3);
        var lt = goals.get(0);
        var eq = goals.get(1);
        var gt = goals.get(2);

        var opLT = intLdt.getLessThan();
        var opGT = intLdt.getGreaterThan();

        lt.addFormula(new SequentFormula(tb.func(opLT, params.on, intLdt.zero())), true, true);
        eq.addFormula(new SequentFormula(tb.equals(params.on, intLdt.zero())), true, true);
        gt.addFormula(new SequentFormula(tb.func(opGT, params.on, intLdt.zero())), true, true);

        var engine = stateMap.getEngine();
        if (params.lessThan0 != null && params.lessThan0.isNotEmpty()) {
            stateMap.setGoal(lt);
            engine.execute(uiControl, params.lessThan0);
        }

        if (params.equals0 != null && params.equals0.isNotEmpty()) {
            stateMap.setGoal(eq);
            engine.execute(uiControl, params.equals0);
        }

        if (params.greaterThan0 != null && params.greaterThan0.isNotEmpty()) {
            stateMap.setGoal(gt);
            engine.execute(uiControl, params.greaterThan0);
        }

        // TODO select which goal after execution?

    }

    @Override
    public String getName() {
        return "integer-split";
    }

    @Override
    public List<String> getAliases() {
        return List.of(
                "isplit", "integerSplit"
        );
    }

    @Override
    public String getDocumentation() {
        return "";
    }

    public static class Parameters {
        @Option("<0")
        @Nullable
        ScriptBlock lessThan0;

        @Option("=0")
        @Nullable
        ScriptBlock equals0;

        @Option(">0")
        @Nullable
        ScriptBlock greaterThan0;

        @Argument
        @Documentation("The variable to make the case distinction on")
        @MonotonicNonNull
        JTerm on;
    }
}
