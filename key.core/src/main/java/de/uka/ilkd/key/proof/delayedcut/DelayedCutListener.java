package de.uka.ilkd.key.proof.delayedcut;

/**
 * Interface for DelayedCut listeners.
 *
 * @see DelayedCut
 * @see DelayedCutProcessor
 * @author Benjamin Niedermann
 */
public interface DelayedCutListener {
    void eventCutting();

    void eventRebuildingTree(int currentTacletNumber, int totalNumber);

    void eventEnd(DelayedCut cutInformation);

    void eventException(Throwable throwable);
}
