package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.benchmarks.LLMChoice;
import org.key_project.llmsynth.benchmarks.LLMTask;

import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyFunction;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyLoopInvariant;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifySubcontract;
import org.key_project.llmsynth.prompts.IPromptStrategy;
import org.key_project.llmsynth.prompts.PromptAnswer;
import org.key_project.llmsynth.prompts.PromptReason;
import org.key_project.llmsynth.prompts.PromptResult;
import org.key_project.llmsynth.verificators.LegacyVerificator;

import java.nio.file.Path;
import java.util.function.BiFunction;
import java.util.function.Function;

public final class LegacyStrategyProvider {
    public final class SP<TTask extends LLMTask> implements StrategyProvider<TTask, Nothing> {
        BiFunction<LLMChoice, TTask, IPromptStrategy<PromptReason, Nothing>>  mkstrategy;
        BiFunction<LLMChoice, TTask, Function<PromptAnswer, PromptResult>> mkverificator;

        public SP(BiFunction<LLMChoice, TTask, IPromptStrategy<PromptReason, Nothing>> mkstrategy, BiFunction<LLMChoice, TTask, Function<PromptAnswer, PromptResult>> mkverificator) {
            this.mkstrategy = mkstrategy;
            this.mkverificator = mkverificator;
        }

        public IPromptStrategy<PromptReason, Nothing> selectStrategy(LLMChoice oracle, TTask task) {
            return mkstrategy.apply(oracle, task);
        }

        public Nothing createUserData() {
            return Nothing.getInstance();
        }

        public Function<PromptAnswer, PromptResult> createDefaultVerificator(LLMChoice oracle, TTask task) {
            return mkverificator.apply(oracle, task);
        }
    }

    private final StrategyProvider<TaskSpecifyFunction, Nothing> tsf;
    private final StrategyProvider<TaskSpecifySubcontract, Nothing> tss;
    private final StrategyProvider<TaskSpecifyLoopInvariant, Nothing> tsli;

    public LegacyStrategyProvider(Path tmpfile) {
        tsf = new SP<>(this::specFunctionStrategy, (oracle, task) -> {
            var verificator = new LegacyVerificator(
                    task.classInfo.getClassLines(),
                    task.methodInfo.getName(),
                    false, null, false, tmpfile);
            return verificator::verify;
        });
        tss = new SP<>(this::specSubcontractStrategy, (oracle, task) -> {
            var verificator = new LegacyVerificator(
                    task.classInfo.getClassLines(),
                    task.methodInfo.getName(),
                    false, task.subMethodInfo.getName(), false, tmpfile);
            return verificator::verify;
        });
        tsli = new SP<>(this::specLoopinvariantStrategy, (oracle, task) -> {
            var verificator = new LegacyVerificator(
                    task.classInfo.getClassLines(),
                    task.methodInfo.getName(),
                    false, null, true, tmpfile);
            return verificator::verify;
        });
    }

    public StrategyProvider<TaskSpecifyFunction, Nothing> getTaskSpecifyFunctionProvider() {
        return tsf;
    }

    public StrategyProvider<TaskSpecifySubcontract, Nothing> getTaskSpecifySubcontractProvider() {
        return tss;
    }

    public StrategyProvider<TaskSpecifyLoopInvariant, Nothing> getTaskSpecifyLoopInvariantProvider() {
        return tsli;
    }

    private Nothing createUserData() {
        return Nothing.getInstance();
    }

    private IPromptStrategy<PromptReason, Nothing> specFunctionStrategy(LLMChoice oracle, TaskSpecifyFunction task) {
        return new LegacySpecifyTopLevelStrategy(task.classInfo, task.methodInfo).broaden();
    }

    private IPromptStrategy<PromptReason, Nothing> specSubcontractStrategy(LLMChoice oracle, TaskSpecifySubcontract task) {
        return new LegacySpecifySubcontractStrategy(task.classInfo, task.methodInfo, task.subMethodInfo).broaden();
    }

    private IPromptStrategy<PromptReason, Nothing> specLoopinvariantStrategy(LLMChoice oracle, TaskSpecifyLoopInvariant task) {
        return new LegacySpecifyLoopinvariantStrategy(task.classInfo, task.methodInfo).broaden();
    }
}
