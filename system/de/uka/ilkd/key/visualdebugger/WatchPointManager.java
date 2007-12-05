package de.uka.ilkd.key.visualdebugger;

import java.util.LinkedList;

/**
 * The Class WatchPointManager keeps a list of all watchpoints.
 */
public class WatchPointManager {

    /** The watch points. */
    private LinkedList watchPoints = new LinkedList();

    /**
     * Gets the watch points.
     * 
     * @return the watch points
     */
    public LinkedList getWatchPoints() {
        return watchPoints;
    }
    
    /**
     * Gets the watch points as array.
     * 
     * @return the watch points as array
     */
    public Object[] getWatchPointsAsArray() {
        return  watchPoints.toArray();
    }
    
    /**
     * Adds the watch point.
     * 
     * @param wp the wp
     */
    public void addWatchPoint(WatchPoint wp){
        watchPoints.add(wp);
    }
    
    /**
     * Removes the watch point.
     * 
     * @param wp the wp
     */
    public void removeWatchPoint(WatchPoint wp){
        
       if (watchPoints.contains(wp)){
           watchPoints.remove(wp);
       }
    }
}
