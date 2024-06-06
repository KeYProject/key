package org.key_project.llmsynth.verificators;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import jdk.dynalink.linker.MethodHandleTransformer;
import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.benchmarks.LLMChoice;
import org.key_project.llmsynth.benchmarks.legacy.*;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyFunction;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifyLoopInvariant;
import org.key_project.llmsynth.benchmarks.tasks.TaskSpecifySubcontract;
import org.key_project.llmsynth.old_unused.Gpt3Prompt;
import org.key_project.llmsynth.prompts.PromptAnswer;
import org.key_project.llmsynth.prompts.PromptReason;
import org.key_project.llmsynth.prompts.PromptResult;


import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.*;
import java.util.function.Consumer;
import java.util.function.Function;

public class LegacyVerificator implements Function<PromptAnswer, PromptResult> {
    List<String> classLines;
    String methodName;
    boolean isCtor;
    String subfun;
    boolean specInvariant;
    int maxTries;
    Path tmpFile;

    public LegacyVerificator(List<String> classLines, String methodName, boolean isCtor, String subfun, boolean specInvariant, Path tmpFile) {
        this.classLines = classLines;
        this.methodName = methodName;
        this.isCtor = isCtor;
        this.subfun = subfun;
        this.specInvariant = specInvariant;
        this.tmpFile = tmpFile; // todo: what to do with this one...
    }

    class AutoClose<T> implements AutoCloseable {
        public final T val;
        private final Consumer<T> close;
        public AutoClose(T inner, Consumer<T> close) {
            this.val = inner;
            this.close = close;
        }

        @Override
        public void close() {
            close.accept(val);
        }
    }

    private Gpt3Prompt.Triple<Boolean, Gpt3Prompt.FailureReason, Exception> getKeyCheckResult(String jml_text, Gpt3Prompt.FailureReason err_so_far) {
        // key_result = tryKeyValidation(classLines, methodName, possible_jml_text.x, specInvariant, tmpFile, possible_jml_text.y);
        try (AutoClose<ExecutorService> executor = new AutoClose<>(Executors.newSingleThreadExecutor(), ExecutorService::shutdown)) {
            int timeout = 100; // todo: this is parameterized by the benchmark
            TimeUnit timeUnit = TimeUnit.SECONDS;
            Future<Gpt3Prompt.Triple<Boolean, Gpt3Prompt.FailureReason, Exception>> fut = executor.val.submit(
                    () -> Gpt3Prompt.tryKeyValidation(classLines, methodName, subfun, jml_text, specInvariant, tmpFile, err_so_far));
            try {
                var kr = fut.get(timeout, timeUnit);
                return new Gpt3Prompt.Triple<>(kr.x, kr.y, kr.z);
            } catch (TimeoutException | InterruptedException | RuntimeException | ExecutionException e) {
                System.out.println(e);
                System.out.println(e.getStackTrace());
                return new Gpt3Prompt.Triple<>(false, Gpt3Prompt.FailureReason.INVALID_JAVA, null);
            }
        }
    }

    public PromptResult verify(PromptAnswer answer) {
        String content = answer.getContent();

        String methodToSearch = subfun != null ? subfun : methodName;
        ;
        // Extract the JML from the prompt answer
        Gpt3Prompt.Pair<String, Gpt3Prompt.FailureReason> possible_jml_text;
        if (specInvariant) {
            possible_jml_text = Gpt3Prompt.extractInvariant(content, methodToSearch);
        } else {
            possible_jml_text = Gpt3Prompt.extractJML(content, methodToSearch);
        }

        // Perform the validation
        Gpt3Prompt.FailureReason failureReason;
        Exception failureException;
        boolean keyVerifiedSuccessfully;

        if (possible_jml_text.x == null) {
            failureReason = possible_jml_text.y;
            failureException = null;
            keyVerifiedSuccessfully = false;
        } else {
            String found_jml = possible_jml_text.x;
            Gpt3Prompt.FailureReason err_so_far = possible_jml_text.y;
            Gpt3Prompt.Triple<Boolean, Gpt3Prompt.FailureReason, Exception> key_result =
                    getKeyCheckResult(found_jml, err_so_far);
            keyVerifiedSuccessfully = key_result.x;
            failureReason = key_result.y;
            failureException = key_result.z;
        }

        // Prepare the result
        if (keyVerifiedSuccessfully) {
            return PromptResult.accept(answer);
        } else {
            PromptReason reason;
            switch (failureReason) {
                case NONE:
                    throw new IllegalStateException("There is no reason for failure given, but we're in the failure path.");
                case NO_JML_IN_SEARCH_LOCATIONS:
                    reason = new NoJMlInSearchLocations();
                    break;
                case NO_JML_IN_REGION:
                    reason = new NoJMLInRegion();
                    break;
                case INVALID_JAVA:
                    reason = new InvalidJava();
                    break;
                case WRONG_JML:
                    reason = new WrongJML(possible_jml_text.x, failureException);
                    break;
                case UNKNOWN:
                    reason = new UnknownReason(failureException);
                    break;
                case UNKNOWN_FATAL:
                    throw new RuntimeException("There is no useful response for a fatal error problem");
                default:
                    throw new RuntimeException("Unknown legacy reason");
            }
            return PromptResult.reject(answer, reason);
        }
    }

    public PromptResult apply(PromptAnswer answer) {
        return verify(answer);
    }

    public static LegacyVerificator fromTask(LLMChoice oracle, TaskSpecifyLoopInvariant task, Path tmpfile) {
        return new LegacyVerificator(
                task.classInfo.getClassLines(),
                task.methodInfo.getName(),
                false, null, true, tmpfile);
    }

    public static LegacyVerificator fromTask(LLMChoice oracle, TaskSpecifySubcontract task, Path tmpfile) {
        return new LegacyVerificator(
                task.classInfo.getClassLines(),
                task.methodInfo.getName(),
                false, task.subMethodInfo.getName(), false, tmpfile);
    }

    public static LegacyVerificator fromTask(LLMChoice oracle, TaskSpecifyFunction task, Path tmpfile) {
        return new LegacyVerificator(
                task.classInfo.getClassLines(),
                task.methodInfo.getName(),
                false, null, false, tmpfile);
    }
}
