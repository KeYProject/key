package org.key_project.llmsynth.benchmarks;

import org.key_project.llmsynth.LLMTaskTag;

import java.util.List;

/**
 * Everything relevant to a benchmark is stored here
 */
public class BenchmarkParameters {
    // TODO: assume that this is unique for easier handling? (i.e. use as primary key)
    //  If the suite-version should be retained as well, it needs to be mangled into the tag

    /**
     * The unique identifier of the benchmark (repeated benchmarks not counted)
     */
    public String name;

    /**
     * The oracle to be tested in the benchmark
     */
    public LLMChoice oracle;

    /**
     * Parameters that vary the behaviour of the BenchmarkRunner/Search-tree exploration
     */
    public ControlParameters controlParameters;

    /**
     * The task this benchmark is supposed to solve
     */
    public LLMTask task;

}

