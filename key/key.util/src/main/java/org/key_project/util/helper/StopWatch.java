package org.key_project.util.helper;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

/**
 * Facility for measuring java code.
 *
 * @author Alexander Weigl
 * @version 1 (4/29/20)
 */
public class StopWatch {
    private ArrayList<Long> startTimes = new ArrayList<>();
    private ArrayList<String> names = new ArrayList<>();
    private boolean nanoSeconds = false;
    private final boolean measurementsEnabled;
    private Map<String, List<Long>> measurements = new TreeMap<>();

    public StopWatch() {
        this(false);
    }

    public StopWatch(boolean measurementsEnabled) {
        this.measurementsEnabled = measurementsEnabled;
    }


    public long start(String name) {
        if (measurementsEnabled)
            names.add(name);
        long time = getTime();
        startTimes.add(time);
        return time;
    }

    public long start() {
        return start("");
    }

    public long stop() {
        long stop = getTime();
        long start = startTimes.remove(startTimes.size() - 1);
        long duration = stop - start;
        if (measurementsEnabled) {
            String key = names.remove(names.size() - 1);
            List<Long> values = measurements.computeIfAbsent(key, (k) -> new ArrayList<>());
            values.add(duration);
        }
        return duration;
    }

    private long getTime() {
        if (nanoSeconds) {
            return System.nanoTime();
        } else {
            return System.currentTimeMillis();
        }
    }

    public boolean isNanoSeconds() {
        return nanoSeconds;
    }

    public void setNanoSeconds(boolean nanoSeconds) {
        this.nanoSeconds = nanoSeconds;
    }

    public boolean isMeasurementsEnabled() {
        return measurementsEnabled;
    }

    public Map<String, List<Long>> getMeasurements() {
        return measurements;
    }

    public void setMeasurements(Map<String, List<Long>> measurements) {
        this.measurements = measurements;
    }
}
