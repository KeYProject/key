package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.benchmarks.LLMChoice;
import org.key_project.llmsynth.benchmarks.LLMTask;

import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyFunction;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyLoopInvariant;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifySubcontract;
import org.key_project.llmsynth.prompts.ISearchStrategy;
import org.key_project.llmsynth.prompts.VerificationResult;
import org.key_project.llmsynth.verificators.LegacyVerificator;

import java.nio.file.Path;
import java.util.function.BiFunction;
import java.util.function.Function;

/**
 * A Factory of StrategyProviders for the old quick-n-dirty benchmarking method
 */
public final class LegacyInterfaceFactory {
    public final class SP<TTask extends LLMTask> implements StrategyProvider<TTask, Nothing> {
        BiFunction<LLMChoice, TTask, ISearchStrategy<Nothing>>  mkstrategy;
        BiFunction<LLMChoice, TTask, Function<Prompt, VerificationResult>> mkverificator;

        public SP(BiFunction<LLMChoice, TTask, ISearchStrategy<Nothing>> mkstrategy, BiFunction<LLMChoice, TTask, Function<Prompt, VerificationResult>> mkverificator) {
            this.mkstrategy = mkstrategy;
            this.mkverificator = mkverificator;
        }

        public ISearchStrategy<Nothing> selectStrategy(LLMChoice oracle, TTask task) {
            return mkstrategy.apply(oracle, task);
        }

        public Nothing createUserData() {
            return Nothing.getInstance();
        }

        public Function<Prompt, VerificationResult> createDefaultVerificator(LLMChoice oracle, TTask task) {
            return mkverificator.apply(oracle, task);
        }
    }

    private final StrategyProvider<TaskSpecifyFunction, Nothing> tsf;
    private final StrategyProvider<TaskSpecifySubcontract, Nothing> tss;
    private final StrategyProvider<TaskSpecifyLoopInvariant, Nothing> tsli;

    public LegacyInterfaceFactory(Path tmpfile) {
        tsf = new SP<TaskSpecifyFunction>(this::specFunctionStrategy, (oracle, task) -> {
            var verificator = new LegacyVerificator(
                    task.classInfo.getClassLines(),
                    task.methodInfo.getName(),
                    false, null, false, tmpfile);
            return verificator::verify;
        });
        tss = new SP<TaskSpecifySubcontract>(this::specSubcontractStrategy, (oracle, task) -> {
            var verificator = new LegacyVerificator(
                    task.classInfo.getClassLines(),
                    task.methodInfo.getName(),
                    false, task.subMethodInfo.getName(), false, tmpfile);
            return verificator::verify;
        });
        tsli = new SP<TaskSpecifyLoopInvariant>(this::specLoopinvariantStrategy, (oracle, task) -> {
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

    private ISearchStrategy<Nothing> specFunctionStrategy(LLMChoice oracle, TaskSpecifyFunction task) {
        return new LegacySpecifyTopLevelStrategy(task.classInfo, task.methodInfo);
    }

    private ISearchStrategy<Nothing> specSubcontractStrategy(LLMChoice oracle, TaskSpecifySubcontract task) {
        return new LegacySpecifySubcontractStrategy(task.classInfo, task.methodInfo, task.subMethodInfo);
    }

    private ISearchStrategy<Nothing> specLoopinvariantStrategy(LLMChoice oracle, TaskSpecifyLoopInvariant task) {
        return new LegacySpecifyLoopinvariantStrategy(task.classInfo, task.methodInfo);
    }
}
