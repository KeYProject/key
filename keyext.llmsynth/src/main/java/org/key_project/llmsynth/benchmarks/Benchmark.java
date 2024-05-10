package org.key_project.llmsynth.benchmarks;

public class Benchmark {
    public final BenchmarkParameters params;
    public int n; // this benchmark is the n-th benchmark with the same params ; TODO: should this really be used?
    private BenchmarkResult result;

    public Benchmark(BenchmarkParameters bp) {
        params = bp;
    }

    public boolean isFinished() {
        return result != null;
    }

    public BenchmarkResult getResult() {
        return result;
    }

    public void complete(BenchmarkResult result) {
        if (result != null)
            throw new IllegalStateException("This Benchmark is already completed");
        this.result = result;
    }
}
