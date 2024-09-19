package org.key_project.isabelletranslation;

public interface IsabelleSolverListener extends IsabelleLauncherListener {
    void parsingStarted(IsabelleSolver solver, IsabelleProblem problem);

    void parsingFinished(IsabelleSolver solver, IsabelleProblem problem);

    void parsingFailed(IsabelleSolver solver, IsabelleProblem problem, Exception e);

    void buildingStarted(IsabelleSolver solver, IsabelleProblem problem);

    void buildingFinished(IsabelleSolver solver, IsabelleProblem problem);

    void buildingFailed(IsabelleSolver solver, IsabelleProblem problem, Exception e);

    void processStarted(IsabelleSolver solver, IsabelleProblem problem);

    void processInterrupted(IsabelleSolver solver, IsabelleProblem problem, Exception e);

    void processStopped(IsabelleSolver solver, IsabelleProblem problem);

    void processTimeout(IsabelleSolver solver, IsabelleProblem problem);

    void sledgehammerStarted(IsabelleSolver solver, IsabelleProblem problem);

    void sledgehammerFinished(IsabelleSolver solver, IsabelleProblem problem);

    void sledgehammerFailed(IsabelleSolver solver, IsabelleProblem problem, Exception e);
}
