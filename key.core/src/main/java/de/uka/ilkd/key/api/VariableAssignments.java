/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import java.util.HashMap;
import java.util.Map;

/**
 * Class to represent current Variable assigments. Created by S.Grebing
 */
public class VariableAssignments {


    public enum VarType {
        INT("\\term int"), BOOL("\\term bool"), ANY("\\term any"), INT_ARRAY("\\term int[]"),
        OBJECT("\\term Object"), HEAP("\\term Heap"), FIELD("\\term Field"),
        LOCSET("\\term LocSet"), FORMULA("\\formula"), SEQ("\\term Seq");

        private final String declPrefix;

        VarType(String declPrefix) {
            this.declPrefix = declPrefix;
        }

        public String getKeYDeclarationPrefix() {
            return declPrefix;
        }
    }

    /**
     * Reference to parent assignments
     */
    private final VariableAssignments parent;

    /**
     * Current Assignments
     */
    private final Map<String, Object> currentAssignments;

    /**
     * Type Map of assignments
     */
    private final Map<String, VariableAssignments.VarType> typeMap;

    /**
     * Create new, empty variable assignment, to add variables
     *
     * @param parent
     */
    public VariableAssignments(VariableAssignments parentAssignments) {
        this.currentAssignments = new HashMap<>();
        this.typeMap = new HashMap<>();
        this.parent = parentAssignments;
    }


    /**
     * Default constructor
     */
    public VariableAssignments() {
        this.currentAssignments = new HashMap<>();
        this.typeMap = new HashMap<>();
        this.parent = null;
    }


    /**
     * Get the value of a stored variable name TODO Exception spezifischer
     *
     * @param varName
     * @return Value of variable
     */
    public Object getVarValue(String varName) throws Exception {
        if (currentAssignments.containsKey(varName)) {
            return currentAssignments.get(varName);
        } else {
            if (parent != null) {
                return parent.getVarValue(varName);
            } else {
                throw new Exception("Variable " + varName + " could not be found");
            }
        }
    }

    /**
     * Add a variable assignment with type and value
     *
     * @param varName
     * @param value
     * @param type
     */
    public void addAssignmentWithType(String varName, Object value, VarType type) {
        typeMap.put(varName, type);
        currentAssignments.put(varName, value);

    }

    /**
     * Add a variable assignment without type
     *
     * @param varName
     * @param value
     */
    public void addAssignment(String varName, Object value) throws Exception {
        if (typeMap.containsKey(varName)) {
            currentAssignments.put(varName, value);
        } else {
            throw new Exception("Variable " + varName + "must be declared first");
        }

    }

    /**
     * TODO better exception Add a new type declaration
     *
     * @param varName
     * @param type
     */
    public void addType(String varName, VarType type) throws Exception {
        if (typeMap.containsKey(varName)) {
            if (typeMap.get(varName) != type) {
                throw new Exception("Variable " + varName + "was already declared with type "
                    + typeMap.get(varName).toString());
            }
        } else {
            typeMap.put(varName, type);
        }
    }

    /**
     * Returns the map of ID -> Type mappings
     *
     * @return
     */
    public Map<String, VariableAssignments.VarType> getTypeMap() {
        return this.typeMap;
    }


    /*
     * public Object getValue(String name) { return null; }
     *
     * public Type getType() { return null; }
     *
     * public void setType(Type type) {
     *
     * }
     *
     * public void setValue(String name) {
     *
     * }
     */
}
