package org.key_project.llmsynth.benchmarks.tasks;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.LLMTaskTag;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.benchmarks.LLMTask;
import org.key_project.llmsynth.prompts.PromptStrategy;

public class TaskSpecifySubcontract extends LLMTask {
    public final ClassInfo classInfo;
    public final MethodInfo methodInfo;
    public final MethodInfo subMethodInfo;

    public TaskSpecifySubcontract(ClassInfo classInfo, MethodInfo methodInfo, MethodInfo subMethodInfo) {
        super(LLMTaskTag.SPECIFY_SUBCONTRACT);
        this.classInfo = classInfo;
        this.methodInfo = methodInfo;
        this.subMethodInfo = subMethodInfo;
    }
}
