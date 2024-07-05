package org.key_project.llmsynth.benchmarks.tasks;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.LLMTaskTag;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.benchmarks.LLMTask;

/**
 * The task is to specify a contract for a method without further information
 */
public class TaskSpecifyFunction extends LLMTask {
    /**
     * The class in question
     */
    public final ClassInfo classInfo;

    /**
     * The method to be provided with a contract
     */
    public final MethodInfo methodInfo;

    public TaskSpecifyFunction(ClassInfo classInfo, MethodInfo methodInfo) {
        super(LLMTaskTag.SPECIFY_FUNCTION);
        this.classInfo = classInfo;
        this.methodInfo = methodInfo;
    }
}
