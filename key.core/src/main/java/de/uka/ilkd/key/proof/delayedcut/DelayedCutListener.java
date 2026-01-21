package de.uka.ilkd.key.proof.delayedcut;

/**
 * Interface for DelayedCut listeners.
 *
 * @see DelayedCut
 * @see DelayedCutProcessor
 * @author Benjamin Niedermann
 */
public interface DelayedCutListener {
    public void eventCutting();

    public void eventRebuildingTree(int currentTacletNumber, int totalNumber);

    public void eventEnd(DelayedCut cutInformation);

    public void eventException(Throwable throwable);
}
