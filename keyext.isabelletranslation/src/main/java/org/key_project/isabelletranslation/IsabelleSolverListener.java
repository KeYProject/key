package org.key_project.isabelletranslation;

public interface IsabelleSolverListener {
    void processStarted(IsabelleSolver solver, IsabelleProblem problem);

    void processError(IsabelleSolver solver, IsabelleProblem problem, Exception e);

    void processStopped(IsabelleSolver solver, IsabelleProblem problem);
}
