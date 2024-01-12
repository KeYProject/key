/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.model;

import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.ProblemTypeInformation;
import de.uka.ilkd.key.smt.SMTObjTranslator;
import de.uka.ilkd.key.smt.lang.SMTSort;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Represents an SMT model.
 *
 * @author mihai
 *
 */
public class Model {
    private static final Logger LOGGER = LoggerFactory.getLogger(Model.class);

    /**
     * marks an empty model
     */
    private boolean empty;

    /**
     * Maps constant names to constant values. (constantName, constantValue)
     */
    private Map<String, String> constants;
    /**
     * Maps constant values to constant names. (constantValue, constantName1/constantName2/...)
     */
    private final Map<String, String> reversedConstants;
    /**
     * List of heaps.
     */
    private final List<Heap> heaps;
    /**
     * List of location sets.
     */
    private final List<LocationSet> locsets;
    /**
     * List of sequences.
     */
    private final List<Sequence> sequences;
    /**
     * Type information from the SMT specification.
     */
    private ProblemTypeInformation types;

    /**
     * creates an empty SMT model
     */
    public Model() {
        empty = true;
        constants = new HashMap<>();
        heaps = new LinkedList<>();
        locsets = new LinkedList<>();
        reversedConstants = new HashMap<>();
        sequences = new LinkedList<>();
    }

    /**
     * returns true if the model is empty
     *
     * @return true if the model is empty
     */
    public boolean isEmpty() {
        return empty;
    }

    /**
     * marks the model as empty or full
     *
     * @param empty indicates model status
     */
    public void setEmpty(boolean empty) {
        this.empty = empty;
    }

    /**
     * Transforms an Object id from binary form to #on, where n is a decimal number.
     *
     * @param objectID object id in binary form
     * @return #on, where n is a decimal number.
     */
    private String processObjectID(String objectID) {
        objectID = objectID.replace("#", "");
        objectID = objectID.replace("b", "");
        int i = Integer.parseInt(objectID, 2);
        return "#o" + i;
    }

    /**
     * Transforms a sequence id from binary form to #sn, where n is a decimal number.
     *
     * @param sequenceID sequence id in binary form
     * @return #sn, where n is a decimal number.
     */
    private String processSeqID(String sequenceID) {
        sequenceID = sequenceID.replace("#", "");
        sequenceID = sequenceID.replace("b", "");
        int i = Integer.parseInt(sequenceID, 2);
        return "#s" + i;
    }

    /**
     * returns map from constant names to constant values
     *
     * @return map from constant names to constant values
     */
    public Map<String, String> getConstants() {
        return constants;
    }

    /**
     * Rewrites the values of location sets from binary/hexadecimal to a human readable form.
     */
    private void processLocSetNames() {

        SMTSort locsetSort = this.getTypes().getSort(SMTObjTranslator.LOCSET_SORT);
        SMTSort objectSort = this.getTypes().getSort(SMTObjTranslator.OBJECT_SORT);
        SMTSort fieldSort = this.getTypes().getSort(SMTObjTranslator.FIELD_SORT);
        // for all locsets
        for (LocationSet ls : locsets) {
            String name = ls.getName();
            // rewrite the name of the location set
            name = processConstantValue(name, locsetSort);
            ls.setName(name);

            // for all locations
            for (int i = 0; i < ls.size(); ++i) {

                Location l = ls.get(i);
                // rewrite object name
                String obj = l.getObjectID();
                obj = processConstantValue(obj, objectSort);
                l.setObjectID(obj);

                // rewrite field name
                String f = l.getFieldID();
                if (f.startsWith("#b") || f.startsWith("#x")) {
                    f = processConstantValue(f, fieldSort);
                    String fieldNo = f.replace("#", "").replace("f", "");
                    f = "[" + fieldNo + "]";
                    l.setFieldID(f);
                }

            }

        }

    }

    /**
     * Rewrite the object names from binary/hexadecimal to a human readable form.
     */
    public void processObjectNames() {
        for (Heap h : heaps) {
            for (ObjectVal ov : h.getObjects()) {
                String newName = processObjectID(ov.getName());
                ov.setName(newName);
            }
        }
    }

    /**
     * Rewrite the sequence names from binary/hexadecimal to a human readable form.
     */
    public void processSequenceNames() {
        for (Sequence s : sequences) {
            String newName = processSeqID(s.getName());
            s.setName(newName);
        }
    }

    /**
     *
     * @return the heaps
     */
    public List<Heap> getHeaps() {
        return heaps;
    }

    /**
     *
     * @return the sequences
     */
    public List<Sequence> getSequences() {
        return sequences;
    }

    /**
     *
     * @return the locsets
     */
    public List<LocationSet> getLocsets() {
        return locsets;
    }

    /**
     * @return the types
     */
    public ProblemTypeInformation getTypes() {
        return types;
    }

    /**
     * @param types the types to set
     */
    public void setTypes(ProblemTypeInformation types) {
        this.types = types;
    }

    /**
     * Fills the reversed constants table.
     */
    private void fillReversedTable() {
        reversedConstants.clear();
        for (Entry<String, String> e : constants.entrySet()) {

            String value = e.getValue();
            String constant = e.getKey();

            if (reversedConstants.containsKey(value)) {
                constant = reversedConstants.get(value) + "/" + constant;
            }
            reversedConstants.put(value, constant);
        }
    }

    /**
     * Adds a constant to the model.
     *
     * @param key the constant name
     * @param value the constant value
     */
    public void addConstant(String key, String value) {
        constants.put(key, value);
    }

    /**
     * Adds a heap to the model.
     *
     * @param e The heap to be added
     */
    public void addHeap(Heap e) {
        heaps.add(e);
    }

    /**
     * Adds a location set to the model.
     *
     * @param e The location set to be added.
     */
    public void addLocationSet(LocationSet e) {
        locsets.add(e);
    }

    /**
     * Adds a sequence set to the model.
     *
     * @param s The sequence to be added.
     */
    public void addSequence(Sequence s) {
        sequences.add(s);
    }

    /**
     * Transforms a binary value of an any to a human readable form: #sn, where s is the first
     * letter of the actual sort name and n is the decimal value of corresponding to the any value
     * after the removal of the three type bits and the fill up bits.
     *
     * @param val original any value
     * @param s actual sort of the any sort
     * @return formatted value
     */
    private String formatAny(String val, SMTSort s) {

        val = val.substring(3);
        long bitSize = s.getBitSize();
        val = val.substring(val.length() - (int) bitSize);
        int x = Integer.parseInt(val, 2);
        val = "#" + s.getId().charAt(0) + x;
        val = val.toLowerCase();
        return val;
    }

    /**
     * Transforms a constant value from binary/hexadecimal form to a human redable form.
     *
     * @param val binary/hexadecimal value of constant
     * @param s sort of constant
     * @return human readable form #sn with s the first letter of the sort of the constant, and n
     *         the decimal value of the constant
     */
    public String processConstantValue(String val, SMTSort s) {
        if (val.equals("true") || val.equals("false")) {
            return val;
        }

        if (val.startsWith("#x")) {
            val = val.replace("#", "").replace("x", "");
            val = "#b" + Integer.toBinaryString(Integer.parseInt(val, 16));
        }

        val = val.replace("#", "").replace("b", "");
        int x = Integer.parseInt(val, 2);

        if (s.getId().equals(SMTObjTranslator.BINT_SORT)) {
            long intBound = types.getSort(SMTObjTranslator.BINT_SORT).getBound();
            if (x >= intBound / 2) {
                x = (int) (x - intBound);
            }
            val = Integer.toString(x);
            return val;
        }
        val = "#" + s.getId().charAt(0) + x;
        val = val.toLowerCase();
        return val;
    }

    /**
     * Transforms a binary value of an any to a human readable form: #sn, where s is the first
     * letter of the actual sort name and n is the decimal value of corresponding to the any value
     * after the removal of the three type bits and the fill up bits.
     *
     * @param val the original any value in binary/hexadecimal
     * @return the formatted value
     */
    public String processAnyValue(String val) {
        if (val == null) {
            return null;
        }
        // if val is in hexadecimal transform it to binary first
        if (val.startsWith("#x")) {
            val = val.replace("#", "");
            val = val.replace("x", "");
            int x = Integer.parseInt(val, 16);

            long anySize = types.getSort(SMTObjTranslator.ANY_SORT).getBitSize();
            StringBuilder binString = new StringBuilder(Integer.toBinaryString(x));

            while (binString.length() < anySize) {
                binString.insert(0, "0");
            }
            val = "#b" + binString;
        }
        // remove #b prefix of binary string
        val = val.replace("#", "");
        val = val.replace("b", "");

        /*
         * val now contains the binary string, we check the type bits for all possible sort types
         */

        // val is of type bint
        if (val.startsWith(types.getPrefixForSort(types.getSort(SMTObjTranslator.BINT_SORT)))) {
            long intBound = types.getSort(SMTObjTranslator.BINT_SORT).getBound();
            long intSize = types.getSort(SMTObjTranslator.BINT_SORT).getBitSize();
            val = val.substring(3);
            val = val.substring(val.length() - (int) intSize);
            int x = Integer.parseInt(val, 2);

            if (x >= intBound / 2) {
                x = (int) (x - intBound);
            }
            val = Integer.toString(x);
        } else if (val.startsWith(types.getPrefixForSort(SMTSort.BOOL))) {
            // val is of type bool
            val = val.substring(3);
            int x = Integer.parseInt(val, 2);
            if (x == 0) {
                val = "false";
            } else {
                val = "true";
            }
        } else if (val
                .startsWith(types.getPrefixForSort(types.getSort(SMTObjTranslator.SEQ_SORT)))) {
            // val is of type sequence
            val = formatAny(val, types.getSort(SMTObjTranslator.SEQ_SORT));
        } else if (val
                .startsWith(types.getPrefixForSort(types.getSort(SMTObjTranslator.HEAP_SORT)))) {
            // val is of type heap - should never happen!
            val = formatAny(val, types.getSort(SMTObjTranslator.HEAP_SORT));
        } else if (val
                .startsWith(types.getPrefixForSort(types.getSort(SMTObjTranslator.LOCSET_SORT)))) {
            // val is of type location set
            val = formatAny(val, types.getSort(SMTObjTranslator.LOCSET_SORT));
        } else {
            // val can only be of type object
            val = val.substring(3);
            long objSize = types.getSort(SMTObjTranslator.OBJECT_SORT).getBitSize();
            val = val.substring(val.length() - (int) objSize);
            val = "#o" + Integer.parseInt(val, 2);
        }
        return val;
    }

    /**
     * Transforms the values of array fields of objects from binary/hexidecimal to human readable
     * form.
     */
    public void processArrayValues() {
        for (Heap h : heaps) {
            for (ObjectVal o : h.getObjects()) {
                Sort s = o.getSort();
                if (s == null) {
                    continue;
                }

                String sortname = s.name().toString();
                if (!sortname.endsWith("[]")) {
                    continue;
                }

                for (int i = 0; i < o.getLength(); ++i) {
                    String val = o.getArrayValue(i);
                    val = processAnyValue(val);
                    o.setArrayValue(i, val);
                }
            }
        }
    }

    /**
     * Transforms values of sequences from binary/hexadecimal to human readable form
     */
    public void processSeqValues() {
        for (Sequence s : sequences) {
            for (int i = 0; i < s.getLength(); ++i) {
                String val = processAnyValue(s.get(i));
                s.set(i, val);
            }
        }
    }

    /**
     * returns an alias for the given name
     *
     * @param original the name for which an alias is created
     * @return the alias
     */
    private String getAliasedName(String original) {
        return original + "/" + reversedConstants.get(original);
    }

    /**
     * For all values it adds the names of the constants which have the same values.
     */
    public void addAliases() {
        for (Heap h : heaps) {
            for (ObjectVal o : h.getObjects()) {
                if (reversedConstants.containsKey(o.getName())) {
                    o.setName(getAliasedName(o.getName()));
                }
                Map<String, String> newFieldValues = extractFieldValuesFor(o);
                o.setFieldvalues(newFieldValues);
                if (o.getSort() != null && o.getSort().name().toString().endsWith("[]")) {
                    Map<Integer, String> newArrayValues = extractArrayValuesFor(o);
                    o.setArrayValues(newArrayValues);
                }
                Map<String, String> newFunValues = extractFunctionValuesFor(o);
                o.setFunValues(newFunValues);
            }
        }

        for (LocationSet ls : locsets) {
            if (reversedConstants.containsKey(ls.getName())) {
                ls.setName(getAliasedName(ls.getName()));
            }
            List<Location> newLocations = new LinkedList<>();
            for (Location l : ls.getLocations()) {
                String newObjectID =
                    reversedConstants.containsKey(l.getObjectID()) ? getAliasedName(l.getObjectID())
                            : l.getObjectID();
                String newFieldID =
                    reversedConstants.containsKey(l.getFieldID()) ? getAliasedName(l.getFieldID())
                            : l.getFieldID();
                newLocations.add(new Location(newObjectID, newFieldID));
            }
            ls.setLocations(newLocations);
        }

        for (Sequence s : sequences) {
            if (reversedConstants.containsKey(s.getName())) {
                s.setName(getAliasedName(s.getName()));
            }
            for (int i = 0; i < s.getLength(); ++i) {
                if (reversedConstants.containsKey(s.get(i))) {
                    s.set(i, getAliasedName(s.get(i)));
                }
            }
        }
    }

    /**
     * extracts all function values for the specified object
     *
     * @param o the ObjectVal
     * @return set with all function values
     */
    private Map<String, String> extractFunctionValuesFor(ObjectVal o) {
        Map<String, String> newFunValues = new HashMap<>();
        for (Entry<String, String> e : o.getFunValues().entrySet()) {
            if (reversedConstants.containsKey(e.getValue())) {
                newFunValues.put(e.getKey(), getAliasedName(e.getValue()));
            } else {
                newFunValues.put(e.getKey(), e.getValue());
            }
        }
        return newFunValues;
    }

    /**
     * extracts all array values for the specified object
     *
     * @param o the ObjectVal
     * @return set with all array values
     */
    private Map<Integer, String> extractArrayValuesFor(ObjectVal o) {
        Map<Integer, String> newArrayValues = new HashMap<>();
        for (int i = 0; i < o.getLength(); i++) {
            if (reversedConstants.containsKey(o.getArrayValue(i))) {
                newArrayValues.put(i, getAliasedName(o.getArrayValue(i)));
            } else {
                newArrayValues.put(i, o.getArrayValue(i));
            }
        }
        return newArrayValues;
    }

    /**
     * extracts all field values for the specified object
     *
     * @param o the ObjectVal
     * @return set with all field values
     */
    private Map<String, String> extractFieldValuesFor(ObjectVal o) {
        Map<String, String> newFieldValues = new HashMap<>();
        for (Entry<String, String> e : o.getFieldvalues().entrySet()) {
            if (reversedConstants.containsKey(e.getValue())) {
                newFieldValues.put(e.getKey(), getAliasedName(e.getValue()));
            } else {
                newFieldValues.put(e.getKey(), e.getValue());
            }
        }
        return newFieldValues;
    }

    /**
     * returns set of necessary prestate objects
     *
     * @param location
     * @return set of necessary prestate objects
     */
    public Set<ObjectVal> getNecessaryPrestateObjects(String location) {
        Set<ObjectVal> result = new HashSet<>();

        String[] l = location.split("\\.");
        String objName = l[0];
        String nullString = "#o0";

        Heap heap = null;
        for (Heap h : heaps) {
            if (h.getName().equals("heap")) {
                heap = h;
            }
        }
        ObjectVal o = getObject(constants.get(objName), heap);
        int i = 1;
        while (!o.getName().equals(nullString) && i < l.length) {
            result.add(o);
            String pointed = o.getFieldUsingSimpleName(l[i]);
            if (pointed == null) {
                break;
            }
            o = getObject(pointed, heap);
            i++;
        }

        return result;
    }

    /**
     * finds the object the ref parameter is referring to
     *
     * @param ref the reference to the object
     * @return the object the ref parameter is referring to or null otherwise
     */
    public ObjectVal findObject(String ref) {
        String[] l = ref.split("\\.");
        String objName = l[0];
        String nullString = "#o0";

        Heap heap = null;
        for (Heap h : heaps) {
            if (h.getName().equals("heap")) {
                heap = h;
            }
        }
        ObjectVal o = getObject(constants.get(objName), heap);
        int i = 1;
        while (!o.getName().equals(nullString) && i < l.length) {
            String pointed = o.getFieldUsingSimpleName(l[i]);
            if (pointed == null) {
                break;
            }

            o = getObject(pointed, heap);
            i++;
        }

        return o;
    }

    /**
     * cleans up maps from unused/unnecessary objects
     */
    public void removeUnnecessaryObjects() {
        Set<String> objConstants = new HashSet<>();
        for (var pair : constants.entrySet()) {
            var c = pair.getKey();
            if (types.getTypeForConstant(c) == null) {
                continue;
            }
            if (types.getTypeForConstant(c).getId().equals(SMTObjTranslator.OBJECT_SORT)) {
                objConstants.add(pair.getValue());
            }
        }

        for (Heap h : heaps) {
            Set<ObjectVal> reachable = new HashSet<>();
            for (String o : objConstants) {
                reachable.addAll(getReachableObjects(o, h));
            }

            h.getObjects().clear();
            h.getObjects().addAll(reachable);
        }

    }

    /**
     * returns all objects reachable from the specified one in the fiven heap
     *
     * @param name the name of the object from where to look
     * @param heap the heap
     * @return set of reachable objects
     */
    public Set<ObjectVal> getReachableObjects(String name, Heap heap) {

        Set<ObjectVal> result = new HashSet<>();
        ArrayDeque<ObjectVal> scheduled = new ArrayDeque<>();

        ObjectVal init = getObject(name, heap);

        if (init == null) {
            return null;
        }

        scheduled.push(init);

        while (!scheduled.isEmpty()) {
            ObjectVal o = scheduled.pop();

            if (result.contains(o)) {
                continue;
            }

            result.add(o);

            Set<ObjectVal> pointed = pointsTo(o.getName(), heap);

            for (ObjectVal p : pointed) {

                if (result.contains(p)) {
                    continue;
                }

                scheduled.push(p);

            }

        }

        return result;

    }

    /**
     * set of objects the specified object points to
     *
     * @param name the source object
     * @param heap the heap
     * @return set of objects the specified object points to
     */
    public Set<ObjectVal> pointsTo(String name, Heap heap) {

        Set<ObjectVal> result = new HashSet<>();

        ObjectVal o = getObject(name, heap);

        if (o == null) {
            return result;
        }

        for (Entry<String, String> e : o.getFieldvalues().entrySet()) {

            String val = e.getValue();
            ObjectVal pointed = getObject(val, heap);

            if (pointed != null) {
                result.add(pointed);
            }
        }

        for (Entry<Integer, String> e : o.getArrayValues().entrySet()) {

            String val = e.getValue();
            ObjectVal pointed = getObject(val, heap);

            if (pointed != null) {
                result.add(pointed);
            }

        }

        return result;
    }

    /**
     * returns the object of the given name found in the heap
     *
     * @param name the object to look up
     * @param heap the heap
     * @return the object of the given name found in the heap
     */
    public ObjectVal getObject(String name, Heap heap) {
        for (ObjectVal o : heap.getObjects()) {
            if (o.getName().startsWith(name)) {
                return o;
            }
        }

        return null;
    }

    /**
     * removes the pipe character at the start and end from the given string
     *
     * @param s the String to process
     * @return String identical to the parameter except with pipe characters at the start and end
     *         removed
     */
    public static String removePipes(String s) {
        if (s.startsWith("|")) {
            s = s.substring(1);
        }

        if (s.endsWith("|")) {
            s = s.substring(0, s.length() - 1);
        }

        return s;
    }

    /**
     * Transforms the values of constants and object fields from binary/hexadecimal to a human
     * readable from.
     */
    public void processConstantsAndFieldValues() {
        // process constants
        Map<String, String> newConstants = new HashMap<>();
        for (var pair : constants.entrySet()) {
            var c = pair.getKey();
            var value = constants.get(c);
            SMTSort s = types.getTypeForConstant(c);
            if (s == null) {
                LOGGER.warn("No sort for: {}", c);
            } else {
                newConstants.put(c, processConstantValue(value, s));
            }

        }

        constants = newConstants;
        fillReversedTable();

        for (Heap h : heaps) {
            for (ObjectVal o : h.getObjects()) {
                Map<String, String> newFieldValues = new HashMap<>();
                for (String f : o.getFieldvalues().keySet()) {
                    String value = o.getFieldvalues().get(f);
                    newFieldValues.put(f, processAnyValue(value));
                }
                o.setFieldvalues(newFieldValues);
            }
        }
        processLocSetNames();
    }

    /**
     * returns a string representation of this SMT model
     *
     * @return string representation of the model for debugging purposes
     */
    public String toString() {
        StringBuilder result = new StringBuilder("Constants");
        result.append("\n-----------\n\n");
        for (Entry<String, String> e : constants.entrySet()) {
            result.append(e.getKey()).append(" = ").append(e.getValue());
            result.append("\n");
        }

        result.append("\n");
        result.append("\nHeaps");
        result.append("\n-----------");
        for (Heap h : heaps) {
            result.append("\n");
            result.append(h.toString());
        }
        result.append("\n");
        result.append("\nLocation Sets");
        result.append("\n-----------");
        for (LocationSet ls : locsets) {
            result.append("\n");
            result.append(ls.toString());
        }
        result.append("\n");
        result.append("\nSequences");
        result.append("\n-----------");
        for (Sequence s : sequences) {
            result.append("\n").append(s);
        }

        return result.toString();

    }

}
