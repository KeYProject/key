package org.key_project.llmsynth.benchmarks.tasks;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.LLMTaskTag;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.benchmarks.LLMTask;
import org.key_project.llmsynth.prompts.PromptStrategy;

/**
 * Specify a contract for a method called from a method with a contract that is already provided.
 */
public class TaskSpecifySubcontract extends LLMTask {
    /**
     * The class in question
     */
    public final ClassInfo classInfo;

    /**
     * The method with a known contract calling the submethod.
     */
    public final MethodInfo methodInfo;

    /**
     * The called submethod for which a contract is to be found.
     */
    public final MethodInfo subMethodInfo;

    public TaskSpecifySubcontract(ClassInfo classInfo, MethodInfo methodInfo, MethodInfo subMethodInfo) {
        super(LLMTaskTag.SPECIFY_SUBCONTRACT);
        this.classInfo = classInfo;
        this.methodInfo = methodInfo;
        this.subMethodInfo = subMethodInfo;
    }
}
