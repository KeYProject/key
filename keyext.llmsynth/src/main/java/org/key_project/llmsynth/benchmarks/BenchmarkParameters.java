package org.key_project.llmsynth.benchmarks;

import org.key_project.llmsynth.LLMTaskTag;

import java.util.List;

public class BenchmarkParameters {
    // TODO: assume that this is unique for easier handling? (i.e. use as primary key)
    //  If the suite-version should be retained as well, it needs to be mangled into the tag
    public String name;
    public LLMChoice oracle;
    public ControlParameters controlParameters;
    // public List<String> relatedFiles; // TODO: move this into task? (would enable full set-products for a benchmark generator)
    public LLMTask task;

}

