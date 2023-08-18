/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.model;

import java.util.*;

import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Represents an object inside a heap.
 *
 * @author mihai
 *
 */
public class ObjectVal {
    /**
     * The name of the object.
     */
    private String name;
    /**
     * The length of the object.
     */
    private int length;
    /**
     * The sort of the object.
     */
    private Sort sort;
    /**
     * True if object is an exact instance of its sort.
     */
    private boolean exactInstance;
    /**
     * Maps field names to field values.
     */
    private Map<String, String> fieldvalues;
    /**
     * Maps array fields to array values.
     */
    private Map<Integer, String> arrayValues;
    /**
     * Maps function names to function values. Supported functions are model fields and class
     * invariant.
     */
    private Map<String, String> funValues;

    /**
     * creates a new object value of the given name
     *
     * @param name the Object's name
     */
    public ObjectVal(String name) {
        this.name = name;
        fieldvalues = new HashMap<>();
        arrayValues = new HashMap<>();
        funValues = new HashMap<>();
    }

    /**
     * associate the function name with the given value
     *
     * @param fun the name of the function
     * @param val the value to be associated with the specified function
     */
    public void putFunValue(String fun, String val) {
        funValues.put(fun, val);
    }

    /**
     * set the i-th array element to the given value
     *
     * @param i the array index
     * @param val the value
     */
    public void setArrayValue(int i, String val) {
        arrayValues.put(i, val);
    }

    /**
     * returns the i-th array element
     *
     * @param i the index of the array element to be returned
     * @return the value stores at index i
     */
    public String getArrayValue(int i) {
        return arrayValues.get(i);
    }

    /**
     * sets the (exact) dynamic type of this object
     *
     * @param exactInstance the exactInstance to set
     */
    public void setExactInstance(boolean exactInstance) {
        this.exactInstance = exactInstance;
    }

    /**
     * queries whether the (exact) dynamic type of this object is known
     */
    public boolean isExactInstance() {
        return exactInstance;
    }

    /**
     * returns all values stored in this array
     *
     * @return map associating an index with the value stored at that index
     */
    public Map<Integer, String> getArrayValues() {
        return arrayValues;
    }

    /**
     * returns the associated values for the given function names
     *
     * @return map of function name to associated value
     */
    public Map<String, String> getFunValues() {
        return funValues;
    }

    /**
     * sets the name of this entity
     *
     * @param name the name
     */
    public void setName(String name) {
        this.name = name;
    }


    /**
     * queries the name of this entity
     *
     * @return the name
     */
    public String getName() {
        return name;
    }


    /**
     * queries the sort of this entity
     *
     * @return the sort
     */
    public Sort getSort() {
        return sort;
    }

    /**
     * sets the sort of this object/array/function
     *
     * @param sort the sort
     */
    public void setSort(Sort sort) {
        this.sort = sort;
    }

    /**
     * returns the length of this array
     *
     * @return the length
     */
    public int getLength() {
        return length;
    }

    /**
     * sets the length of this array
     *
     * @param length the length
     */
    public void setLength(int length) {
        this.length = length;
    }

    /**
     * @return the fieldvalues
     */
    public Map<String, String> getFieldvalues() {
        return fieldvalues;
    }

    /**
     * @param fieldvalues the fieldvalues to set
     */
    public void setFieldvalues(Map<String, String> fieldvalues) {
        this.fieldvalues = fieldvalues;
    }

    /**
     * returns the currently associated valut to the specified field
     *
     * @param field the field name
     * @return the value associated to the field (or null if no value is known)
     */
    public String get(String field) {
        return fieldvalues.get(field);
    }

    /**
     * associated a field to the given value
     *
     * @param field the field
     * @param value the value assigned to the specified field
     * @return the old value of the field (or null if no value was known before)
     */
    public String put(String field, String value) {
        return fieldvalues.put(field, value);
    }

    /**
     * the value of the field specified by its short name
     *
     * @param name the short name of the field
     * @return the value associated to the field (or null if not known)
     */
    public String getFieldUsingSimpleName(String name) {

        if (fieldvalues.containsKey(name)) {
            return fieldvalues.get(name);
        } else {
            for (var pair : fieldvalues.entrySet()) {
                String field = pair.getKey();
                if (field.endsWith(name) || field.endsWith(name + "|")) {
                    return pair.getValue();
                }
            }
        }
        return null;
    }

    /**
     * textual representation of this object
     *
     * @return the string representation of this object
     */
    public String toString() {
        String tab = "   ";

        // for null we don't care about length, type, etc.
        if (name.startsWith("#o0")) {
            return tab + "Object " + name + "\n";
        }

        String type = sort == null ? "java.lang.Object" : sort.name().toString();

        StringBuilder result = new StringBuilder(tab + "Object " + name + "\n");

        result.append(tab).append(tab).append("length = ").append(length).append("\n");
        result.append(tab).append(tab).append("type =").append(type).append("\n");
        result.append(tab).append(tab).append("exactInstance =").append(this.exactInstance)
                .append("\n");

        List<String> fields = new LinkedList<>(fieldvalues.keySet());
        Collections.sort(fields);

        for (String field : fields) {
            result.append(tab).append(tab).append(field).append(" = ")
                    .append(fieldvalues.get(field));
            result.append("\n");
        }

        for (var pair : funValues.entrySet()) {
            String fun = pair.getKey();
            result.append(tab).append(tab).append(fun).append(" = ").append(pair.getValue());
            result.append("\n");
        }

        List<Integer> arrfields = new ArrayList<>(arrayValues.keySet());
        Collections.sort(arrfields);

        for (int i : arrfields) {
            result.append(tab).append(tab).append("[").append(i).append("] = ")
                    .append(arrayValues.get(i));
            result.append("\n");
        }
        return result.toString();
    }

    /**
     * computes the hashcode of this object
     *
     * @return the hashcode
     */
    @Override
    public int hashCode() {
        return Objects.hashCode(name);
    }


    /**
     * Objects with equal names are equal.
     *
     * @param o the Object to be compared to
     * @return true if this object and o have equal names
     */
    public boolean equals(Object o) {
        if (o instanceof ObjectVal) {
            ObjectVal ov = (ObjectVal) o;
            if (ov.name == null) {
                return name == null;
            }
            return ov.name.equals(name);
        }
        return false;
    }

    /**
     * sets a set of values stored at the indexes of this arrays
     *
     * @param newArrayValues the map associated an array element to its value
     */
    public void setArrayValues(Map<Integer, String> newArrayValues) {
        this.arrayValues = newArrayValues;
    }

    /**
     * sets a set of values to be associated with the given function names
     *
     * @param newFunValues the map associated function names to their respective value
     */
    public void setFunValues(Map<String, String> newFunValues) {
        this.funValues = newFunValues;
    }
}
