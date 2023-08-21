/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.util;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uka.ilkd.key.util.Pair;

/**
 * Simple class to measure the running time of various 'activities'.
 *
 * @author Arne Keller
 */
public final class ExecutionTime {
    /**
     * Mapping: activity name -> start time (milliseconds since unix epoch).
     */
    private final Map<String, Long> startTimes = new LinkedHashMap<>();
    /**
     * Mapping: activity name -> end time.
     */
    private final Map<String, Long> endTimes = new LinkedHashMap<>();

    /**
     * Construct a new execution time tracker.
     */
    public ExecutionTime() {

    }

    /**
     * Begin the given activity. Saves the current time as starting time.
     * The same activity may not be started more than once.
     *
     * @param activity activity name
     */
    public void start(String activity) {
        if (startTimes.containsKey(activity)) {
            throw new IllegalStateException("tried to start already started activity!");
        }
        startTimes.put(activity, System.currentTimeMillis());
    }

    /**
     * Stop the given activity. Saves the current time as end time.
     * The same activity may not be stopped more than once.
     *
     * @param activity activity name
     */
    public void stop(String activity) {
        if (!startTimes.containsKey(activity)) {
            throw new IllegalStateException("tried to end unknown activity!");
        }
        if (endTimes.containsKey(activity)) {
            throw new IllegalStateException("tried to end already stopped activity!");
        }
        endTimes.put(activity, System.currentTimeMillis());
    }

    /**
     * Get a stream of activity names to measured execution times (in milliseconds).
     * Result is ordered by time of start.
     *
     * @return stream of activities to running times
     */
    public Stream<Pair<String, Long>> executionTimes() {
        return startTimes.entrySet().stream()
                .filter(e -> endTimes.containsKey(e.getKey()))
                .map(e -> new Pair<>(e.getKey(), endTimes.get(e.getKey()) - e.getValue()));
    }

    /**
     * Get a mapping of activity names to measured execution times (in milliseconds).
     *
     * @return mapping of activities to running times
     */
    public Map<String, Long> executionTimesMap() {
        return startTimes.entrySet().stream()
                .filter(e -> endTimes.containsKey(e.getKey()))
                .map(e -> new Pair<>(e.getKey(), endTimes.get(e.getKey()) - e.getValue()))
                .collect(Collectors.toUnmodifiableMap(x -> x.first, x -> x.second));
    }
}
