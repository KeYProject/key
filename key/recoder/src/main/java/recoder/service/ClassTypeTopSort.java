// This file is part of the RECODER library and protected by the LGPL.

package recoder.service;

import recoder.abstraction.ClassType;
import recoder.convenience.Format;
import recoder.convenience.Formats;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.List;

abstract class ClassTypeTopSort implements Formats {

    private final List<ClassType> classesDFS = new ArrayList<ClassType>(32);

    private int[] indeg = new int[32];

    protected abstract List<ClassType> getAdjacent(ClassType c);

    private void initIndeg() {
        for (int i = 0; i < indeg.length; i++) {
            indeg[i] = 0;
        }
    }

    private int incrIndeg(int index) {
        while (index >= indeg.length) {
            int[] n = new int[indeg.length * 2];
            System.arraycopy(indeg, 0, n, 0, indeg.length);
            indeg = n;
        }
        return ++indeg[index];
    }

    private int decrIndeg(int index) {
        return --indeg[index];
    }

    private void addClass(ClassType c) {
        if (c != null) {
            int idx = classesDFS.indexOf(c);
            if (idx == -1) {
                classesDFS.add(c);
                idx = classesDFS.size() - 1;
                List<ClassType> neighbors = getAdjacent(c);
                int s = neighbors.size();
                for (int i = 0; i < s; i++) {
                    addClass(neighbors.get(i));
                }
            }
            incrIndeg(idx);
        }
    }

    private void sort(ClassType c, List<ClassType> result) {
        if (c != null) {
            int idx = classesDFS.indexOf(c);
            if (idx == -1) {
                Debug.error(Format.toString("Could not find " + ELEMENT_LONG, c) + "\nList: "
                    + Format.toString("%N", result) + "\n" + Debug.makeStackTrace());
                System.exit(0);
            }
            if (decrIndeg(idx) == 0) {
                result.add(c);
                List<ClassType> neighbors = getAdjacent(c);
                int s = neighbors.size();
                for (int i = 0; i < s; i++) {
                    sort(neighbors.get(i), result);
                }
            }
        }
    }

    public List<ClassType> getAllTypes(ClassType c) {
        initIndeg();
        classesDFS.clear();
        addClass(c);
        List<ClassType> result = new ArrayList<ClassType>(classesDFS.size());
        sort(c, result);
        if (result.size() < classesDFS.size()) {
            throw new RuntimeException("Cyclic inheritance detected!");
        }
        return result;
    }
}
