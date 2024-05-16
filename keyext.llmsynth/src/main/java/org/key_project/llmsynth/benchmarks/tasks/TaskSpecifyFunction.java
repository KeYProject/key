package org.key_project.llmsynth.benchmarks.tasks;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.LLMTaskTag;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.benchmarks.LLMTask;

public class TaskSpecifyFunction extends LLMTask {
    public final ClassInfo classInfo;
    public final MethodInfo methodInfo;

    public TaskSpecifyFunction(ClassInfo classInfo, MethodInfo methodInfo) {
        super(LLMTaskTag.SPECIFY_FUNCTION);
        this.classInfo = classInfo;
        this.methodInfo = methodInfo;
    }
}
