/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.util.ExtList;

import org.key_project.util.collection.Pair;
import recoder.java.declaration.EnumConstantDeclaration;

/**
 * This class is used for wrapping an enum into a standard class type.
 *
 * <p>
 * In addition the programvariables that represent enum constants are memorized. Thus this class is
 * able to have queries on the enum constants.
 *
 * mulbrich: Update 2025 (a mere 19 years later):
 * Updated from the old heap model to the new one.
 *
 * @author mulbrich
 * @since 2006-12-10, updated 2025-10-24 by MU
 */

public class EnumClassDeclaration extends ClassDeclaration {

    /**
     * store the program variables which represent the enum constants
     * in a lookup map from name to (ordinal index, program variable)
     */
    private final Map<String, Pair<@NonNull Integer, @NonNull IProgramVariable>> constants = new HashMap<>();

    /**
     * create a new EnumClassDeclaration that describes an enum defintion. It merely wraps a
     * ClassDeclaration but has memory about which fields have been declared as enum constants.
     *
     * @param children children in the ast (members)
     * @param fullName of the class/enum
     * @param isLibrary see class constructor
     * @param enumConstantDeclarations the declarations for the enum constants
     */
    public EnumClassDeclaration(ExtList children, ProgramElementName fullName, boolean isLibrary,
            List<EnumConstantDeclaration> enumConstantDeclarations) {

        super(children, fullName, isLibrary);

        int ordinal = 0;
        for (EnumConstantDeclaration ecd : enumConstantDeclarations) {
            String constName = ecd.getEnumConstantSpecification().getName();
            constants.put(constName, new Pair<>(ordinal, findAttr(constName)));
            ordinal++;
        }
    }

    /*
     * find the program variable for a constant given by name.
     *
     * The "<Name>::" have to be prepended to obtain the internal name. Throw IllegalStateException
     * if name is not an attribute of this. This will never happen.
     *
     */
    private IProgramVariable findAttr(String fieldName) {
        String completeName = getFullName() + "::" + fieldName;
        for (int i = 0; i < members.size(); i++) {
            if (members.get(i) instanceof FieldDeclaration fd) {
                FieldSpecification fs = fd.getFieldSpecifications().get(0);
                if (fs.getName().equals(completeName)) {
                    return fs.getProgramVariable();
                }
            }
        }
        throw new IllegalStateException(
            fieldName + " is not an attribute of " + this.getFullName());
    }

    /**
     * get the number of defined enum constants in this type.
     *
     * @return the number of defined enum constants in this type
     */
    public int getNumberOfConstants() {
        return constants.size();
    }

    /**
     * get the constant with the given name, including its ordinal index.
     *
     * @param fieldName the name of the enum constant
     * @return a pair of (index, program variable) of the enum constant with the given name or null
     *         if there is no such constant
     */
    public @Nullable Pair<@NonNull Integer, @NonNull IProgramVariable> getConstant(String fieldName) {
        return constants.get(fieldName);
    }
}
