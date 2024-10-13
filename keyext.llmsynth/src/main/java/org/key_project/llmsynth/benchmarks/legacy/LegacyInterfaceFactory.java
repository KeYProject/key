package org.key_project.llmsynth.benchmarks.legacy;

import org.key_project.llmsynth.Nothing;
import org.key_project.llmsynth.benchmarks.LLMChoice;
import org.key_project.llmsynth.benchmarks.LLMTask;

import org.key_project.llmsynth.benchmarks.legacy.codeonly.LegacyCodeOnlySpecifyLoopinvariantStrategy;
import org.key_project.llmsynth.benchmarks.legacy.codeonly.LegacyCodeOnlySpecifySubcontractStrategy;
import org.key_project.llmsynth.benchmarks.legacy.codeonly.LegacyCodeOnlySpecifyTopLevelStrategy;
import org.key_project.llmsynth.benchmarks.legacy.natural.LegacySpecifyNaturalSubcontractStrategy;
import org.key_project.llmsynth.benchmarks.legacy.natural.LegacySpecifyNaturalTopLevelStrategy;
import org.key_project.llmsynth.benchmarks.legacy.standard.LegacySpecifyLoopinvariantStrategy;
import org.key_project.llmsynth.benchmarks.legacy.standard.LegacySpecifySubcontractStrategy;
import org.key_project.llmsynth.benchmarks.legacy.standard.LegacySpecifyTopLevelStrategy;
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
    private final Path tmpfile;

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

    public LegacyInterfaceFactory(Path tmpfile) {
        this.tmpfile = tmpfile;
    }

    public StrategyProvider<TaskSpecifyFunction, Nothing> getTaskSpecifyFunctionProviderGeneral(BiFunction<LLMChoice, TaskSpecifyFunction, ISearchStrategy<Nothing>> mkstrategy) {
        return new SP<TaskSpecifyFunction>(mkstrategy, (oracle, task) -> {
            var verificator = new LegacyVerificator(
                    task.classInfo.getClassLines(),
                    task.methodInfo.getName(),
                    false, null, false, tmpfile);
            return verificator::verify;
        });
    }

    public StrategyProvider<TaskSpecifyFunction, Nothing> getTaskSpecifyFunctionProvider() {
        return getTaskSpecifyFunctionProviderGeneral(this::specFunctionStrategy);
    }

    public StrategyProvider<TaskSpecifyFunction, Nothing> getTaskSpecifyFunctionProviderCodeOnly() {
        return getTaskSpecifyFunctionProviderGeneral(this::specFunctionStrategyCodeOnly);
    }
    public StrategyProvider<TaskSpecifyFunction, Nothing> getTaskSpecifyFunctionProviderNatural() {
        return getTaskSpecifyFunctionProviderGeneral(this::specFunctionStrategyNatural);
    }

    public StrategyProvider<TaskSpecifySubcontract, Nothing> getTaskSpecifySubcontractProviderGeneral(BiFunction<LLMChoice, TaskSpecifySubcontract, ISearchStrategy<Nothing>> mkstrategy) {
        return new SP<TaskSpecifySubcontract>(mkstrategy, (oracle, task) -> {
            var verificator = new LegacyVerificator(
                    task.classInfo.getClassLines(),
                    task.methodInfo.getName(),
                    false, task.subMethodInfo.getName(), false, tmpfile);
            return verificator::verify;
        });
    }

    public StrategyProvider<TaskSpecifySubcontract, Nothing> getTaskSpecifySubcontractProvider() {
        return this.getTaskSpecifySubcontractProviderGeneral(this::specSubcontractStrategy);
    }

    public StrategyProvider<TaskSpecifySubcontract, Nothing> getTaskSpecifySubcontractProviderCodeOnly() {
        return this.getTaskSpecifySubcontractProviderGeneral(this::specSubcontractStrategyCodeOnly);
    }

    public StrategyProvider<TaskSpecifySubcontract, Nothing> getTaskSpecifySubcontractProviderNatural() {
        return this.getTaskSpecifySubcontractProviderGeneral(this::specSubcontractStrategyNatural);
    }

    public StrategyProvider<TaskSpecifyLoopInvariant, Nothing> getTaskSpecifyLoopInvariantProviderGeneral(BiFunction<LLMChoice, TaskSpecifyLoopInvariant, ISearchStrategy<Nothing>> mkstrategy) {
        return new SP<TaskSpecifyLoopInvariant>(mkstrategy, (oracle, task) -> {
            var verificator = new LegacyVerificator(
                    task.classInfo.getClassLines(),
                    task.methodInfo.getName(),
                    false, null, true, tmpfile);
            return verificator::verify;
        });
    }

    public StrategyProvider<TaskSpecifyLoopInvariant, Nothing> getTaskSpecifyLoopInvariantProvider() {
        return this.getTaskSpecifyLoopInvariantProviderGeneral(this::specLoopinvariantStrategy);
    }

    public StrategyProvider<TaskSpecifyLoopInvariant, Nothing> getTaskSpecifyLoopInvariantProviderCodeOnly() {
        return this.getTaskSpecifyLoopInvariantProviderGeneral(this::specLoopinvariantStrategyCodeOnly);
    }

    public StrategyProvider<TaskSpecifyLoopInvariant, Nothing> getTaskSpecifyLoopInvariantProviderNatural() {
        return this.getTaskSpecifyLoopInvariantProviderGeneral(this::specLoopinvariantStrategyNatural);
    }

    private Nothing createUserData() {
        return Nothing.getInstance();
    }

    private ISearchStrategy<Nothing> specFunctionStrategy(LLMChoice oracle, TaskSpecifyFunction task) {
        return new LegacySpecifyTopLevelStrategy(task.classInfo, task.methodInfo);
    }

    private ISearchStrategy<Nothing> specFunctionStrategyCodeOnly(LLMChoice oracle, TaskSpecifyFunction task) {
        return new LegacyCodeOnlySpecifyTopLevelStrategy(task.classInfo, task.methodInfo);
    }

    private ISearchStrategy<Nothing> specFunctionStrategyNatural(LLMChoice oracle, TaskSpecifyFunction task) {
        return new LegacySpecifyNaturalTopLevelStrategy(task.classInfo, task.methodInfo);
    }

    private ISearchStrategy<Nothing> specSubcontractStrategy(LLMChoice oracle, TaskSpecifySubcontract task) {
        return new LegacySpecifySubcontractStrategy(task.classInfo, task.methodInfo, task.subMethodInfo);
    }

    private ISearchStrategy<Nothing> specSubcontractStrategyCodeOnly(LLMChoice oracle, TaskSpecifySubcontract task) {
        return new LegacyCodeOnlySpecifySubcontractStrategy(task.classInfo, task.methodInfo, task.subMethodInfo);
    }

    private ISearchStrategy<Nothing> specSubcontractStrategyNatural(LLMChoice oracle, TaskSpecifySubcontract task) {
        return new LegacySpecifyNaturalSubcontractStrategy(task.classInfo, task.methodInfo, task.subMethodInfo);
    }

    private ISearchStrategy<Nothing> specLoopinvariantStrategy(LLMChoice oracle, TaskSpecifyLoopInvariant task) {
        return new LegacySpecifyLoopinvariantStrategy(task.classInfo, task.methodInfo);
    }

    private ISearchStrategy<Nothing> specLoopinvariantStrategyCodeOnly(LLMChoice oracle, TaskSpecifyLoopInvariant task) {
        return new LegacyCodeOnlySpecifyLoopinvariantStrategy(task.classInfo, task.methodInfo);
    }

    private ISearchStrategy<Nothing> specLoopinvariantStrategyNatural(LLMChoice oracle, TaskSpecifyLoopInvariant task) {
        return new LegacySpecifyNaturalSubcontractStrategy(task.classInfo, task.methodInfo, task.methodInfo);
    }
}
