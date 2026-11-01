/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.declaration;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.logic.JavaDLFieldNames;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;

/**
 * This class is used for wrapping an enum into a standard class type.
 *
 * <p>
 * In addition the programvariables that represent enum constants are memorized. Thus this class is
 * able to have queries on the enum constants.
 *
 * @author mulbrich
 * @since 2006-12-10
 */

@NullMarked
public class EnumClassDeclaration extends ClassDeclaration {

    /**
     * store the program variables which represent the enum constants
     */
    private final List<IProgramVariable> constants = new ArrayList<>();

    /**
     * create a new EnumClassDeclaration that describes an enum defintion. It merely wraps a
     * ClassDeclaration but has memory about which fields have been declared as enum constants.
     *
     * @param children
     *        children in the ast (members)
     * @param fullName
     *        of the class/enum
     * @param isLibrary
     *        see class constructor
     */
    // TODO javaparser
    public EnumClassDeclaration(
            ExtList children, ProgramElementName fullName, boolean isLibrary
    /* , List<EnumConstantDeclaration> enumConstantDeclarations */) {
        super(children, fullName, isLibrary);

        // for (EnumConstantDeclaration ecd : enumConstantDeclarations) {
        // String constName = ecd.getEnumConstantSpecification().getName();
        // constants.add(findAttr(constName));
        // }
    }

    /**
     * find the program variable for a constant given by name.
     *
     * <p>
     * The "<Name>::" have to be prepended to obtain the internal name. Throw IllegalStateException
     * if name is not an attribute of this. This will never happen.
     *
     * <p>
     * A field declaration always has a field specification and that specification a name; the
     * dereferences of the (nullable) specification and its (nullable) name are suppressed with a
     * scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    private IProgramVariable findAttr(String fieldName) {
        String completeName = getFullName() + JavaDLFieldNames.SEPARATOR + fieldName;
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

    /*
     * is pv a enum constant of THIS enum?
     */
    private boolean isLocalEnumConstant(IProgramVariable pv) {
        for (IProgramVariable cnst : constants) {
            if (cnst.equals(pv)) {
                return true;
            }
        }
        return false;
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
            if (constants.get(i).equals(pv)) {
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
     *         <p>
     *         A program variable of an enum-typed attribute always carries a KeY Java type; the
     *         dereference of the (nullable) KeY Java type is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public static boolean isEnumConstant(IProgramVariable attribute) {
        KeYJavaType kjt = attribute.getKeYJavaType();
        Type type = kjt.getJavaType();
        if (type instanceof EnumClassDeclaration) {
            return ((EnumClassDeclaration) type).isLocalEnumConstant(attribute);
        } else {
            return false;
        }
    }

    /**
     * Returns the index of the given program variable amongst the enum constants of any enum type,
     * or {@code -1} if it is not an enum constant.
     *
     * @param attribute ProgramVariable to look up.
     * @return the 0-based index of the constant, or -1 if not found.
     *         <p>
     *         A program variable of an enum-typed attribute always carries a KeY Java type; the
     *         dereference of the (nullable) KeY Java type is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public static int indexOf(ProgramVariable attribute) {
        KeYJavaType kjt = attribute.getKeYJavaType();
        Type type = kjt.getJavaType();
        if (type instanceof EnumClassDeclaration) {
            return ((EnumClassDeclaration) type).localIndexOf(attribute);
        } else {
            return -1;
        }
    }

}
