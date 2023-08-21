/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.model;

import java.util.LinkedList;
import java.util.List;

/**
 * Represents a heap in the SMT model.
 *
 * @author mihai
 *
 */
public class Heap {
    /**
     * The name of the heap.
     */
    final String name;
    /**
     * The contained objects.
     */
    final List<ObjectVal> objects;

    /**
     * Creates a new heap with the given name.
     *
     * @param name
     */
    public Heap(String name) {
        this.name = name;
        objects = new LinkedList<>();
    }

    /**
     * Adds an object to the heap.
     *
     * @param object
     * @return
     */
    public boolean add(ObjectVal object) {
        return objects.add(object);
    }


    public String toString() {
        StringBuilder result = new StringBuilder("Heap " + name + "\n");

        for (ObjectVal o : objects) {
            result.append(o).append("\n");
        }

        return result.toString();

    }

    /**
     * @return the objects
     */
    public List<ObjectVal> getObjects() {
        return objects;
    }


    /**
     *
     * @return the name
     */
    public String getName() {
        return name;
    }

    /**
     * Heaps with equal names are equal.
     */
    public boolean equals(Object that) {

        if (that instanceof Heap) {
            Heap thatHeap = (Heap) that;
            return thatHeap.name.equals(name);
        }


        return false;

    }



}
