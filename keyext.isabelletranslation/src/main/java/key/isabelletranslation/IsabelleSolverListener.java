package key.isabelletranslation;

public interface IsabelleSolverListener {
    void parsingStarted(IsabelleProblem problem);

    void parsingFinished(IsabelleProblem problem);

    void parsingFailed(IsabelleProblem problem, Exception e);

    void buildingStarted(IsabelleProblem problem);

    void buildingFinished(IsabelleProblem problem);

    void buildingFailed(IsabelleProblem problem, Exception e);

    void processStarted(IsabelleProblem problem);

    void processInterrupted(IsabelleProblem problem, Exception e);

    void processStopped(IsabelleProblem problem);

    void processTimeout(IsabelleProblem problem);

    void sledgehammerStarted(IsabelleProblem problem);

    void sledgehammerFinished(IsabelleProblem problem);

    void sledgehammerFailed(IsabelleProblem problem, Exception e);
}
