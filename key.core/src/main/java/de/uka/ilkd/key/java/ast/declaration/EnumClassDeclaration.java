/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import com.github.javaparser.ast.body.EnumConstantDeclaration;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class is used for wrapping an enum into a standard class type.
 *
 * <p>
 * In addition, the programvariables that represent enum constants are memorized. Thus this class is
 * able to have queries on the enum constants.
 *
 * mulbrich: Update 2025 (a mere 19 years later):
 * Updated from the old heap model to the new one.
 *
 * @author mulbrich
 * @since 2006-12-10, updated 2025-10-24 by MU
 */
@NullMarked
public class EnumClassDeclaration extends ClassDeclaration {
    public record EnumEntry(String name, int ordinal, IProgramVariable variable) {
    }

    /**
     * store the program variables which represent the enum constants
     * in a lookup map from name to (ordinal index, program variable)
     */
    private final ImmutableList<EnumEntry> constants;

    /**
     * create a new EnumClassDeclaration that describes an enum defintion. It merely wraps a
     * ClassDeclaration but has memory about which fields have been declared as enum constants.
     *
     * @param children children in the ast (members)
     * @param fullName of the class/enum
     * @param isLibrary see class constructor
     * @param enumConstantDeclarations the declarations for the enum constants
     */
    public EnumClassDeclaration(
            ExtList children, ProgramElementName fullName, boolean isLibrary,
            List<EnumConstantDeclaration> enumConstantDeclarations) {
        super(children, fullName, isLibrary);

        ImmutableList<EnumEntry> seq = ImmutableSLList.nil();
        int ordinal = 0;
        for (EnumConstantDeclaration ecd : enumConstantDeclarations) {
            String constName = ecd.getNameAsString();
            seq = seq.prepend(new EnumEntry(constName, ordinal, findAttr(constName)));
            ordinal++;
        }

        constants = seq;
    }

    /*
     * find the program variable for a constant given by name.
     *
     * The "<Name>::" have to be prepended to obtain the internal name. Throw IllegalStateException
     * if name is not an attribute of this. This will never happen.
     *
     */
    private IProgramVariable findAttr(String fieldName) {
        // TODO String completeName = getFullName() + JavaDLFieldNames.SEPARATOR + fieldName;
        String completeName = getFullName() + "::" + fieldName;
        for (int i = 0; i < members.size(); i++) {
            if (members.get(i) instanceof FieldDeclaration fd) {
                FieldSpecification fs = fd.getFieldSpecifications().get(0);
                if (Objects.equals(fs.getName(), completeName)) {
                    return fs.getProgramVariable();
                }
            }
        }
        throw new IllegalStateException(
            fieldName + " is not an attribute of " + this.getFullName());
    }

    /*
     * is pv a enum constant of THIS enum?
     */
    private boolean isLocalEnumConstant(IProgramVariable pv) {
        return constants.stream().anyMatch(it -> it.variable.equals(pv));
    }

    /**
     * get the index of the program variable amongst the enumconstants of THIS enum.
     *
     * @param pv
     *        PV to look up
     * @return -1 if not found, otherwise the 0-based index.
     */
    private int localIndexOf(ProgramVariable pv) {
        for (int i = 0; i < constants.size(); i++) {
            if (constants.get(i).variable.equals(pv)) {
                return i;
            }
        }
        return -1;
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
     * check whether a PV is an enum constant of any enum type.
     *
     * @param attribute
     *        ProgramVariable to check.
     * @return true iff attribute is an enum constant.
     */
    public static boolean isEnumConstant(IProgramVariable attribute) {
        KeYJavaType kjt = attribute.getKeYJavaType();
        Type type = kjt.getJavaType();
        if (type instanceof EnumClassDeclaration) {
            return ((EnumClassDeclaration) type).isLocalEnumConstant(attribute);
        } else {
            return false;
        }
    }

    // TODO DOC
    public static int indexOf(ProgramVariable attribute) {
        KeYJavaType kjt = attribute.getKeYJavaType();
        Type type = kjt.getJavaType();
        if (type instanceof EnumClassDeclaration) {
            return ((EnumClassDeclaration) type).localIndexOf(attribute);
        } else {
            return -1;
        }
    }


    /**
     * get the constant with the given name, including its ordinal index.
     *
     * @param fieldName the name of the enum constant
     * @return a pair of (index, program variable) of the enum constant with the given name or null
     *         if there is no such constant
     */
    public @Nullable EnumEntry getConstant(String fieldName) {
        return constants.stream().filter(it -> it.name == fieldName).findAny().orElse(null);
    }
}
