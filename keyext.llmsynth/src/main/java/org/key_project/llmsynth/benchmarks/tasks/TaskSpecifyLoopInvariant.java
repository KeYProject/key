package org.key_project.llmsynth.benchmarks.tasks;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.LLMTaskTag;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.benchmarks.LLMTask;

/**
 * The task is to specify a loop invariant in a method
 */
public class TaskSpecifyLoopInvariant extends LLMTask {
    /**
     * The class in question
     */
    public final ClassInfo classInfo;

    /**
     * The method for which the first loop shall be provided with a loop-invariant
     */
    public final MethodInfo methodInfo;

    public TaskSpecifyLoopInvariant(ClassInfo classInfo, MethodInfo methodInfo) {
        super(LLMTaskTag.SPECIFY_LOOP_INVARIANT);
        this.classInfo = classInfo;
        this.methodInfo = methodInfo;
    }
}