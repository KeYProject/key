package de.uka.ilkd.key.proof.delayedcut;

public interface DelayedCutListener {
        public void eventCutting();
        public void eventRebuildingTree(int currentTacletNumber, int totalNumber);
        public void eventEnd(DelayedCut cutInformation); 
        public void eventException(Throwable throwable);
}
