/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.logic.JavaDLFieldNames;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;

import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * This class is used for wrapping an enum into a standard class type.
 *
 * <p>
 * In addition, the programvariables that represent enum constants are memorized. Thus this class is
 * able to have queries on the enum constants.
 *
 * @author mulbrich
 * @since 2006-12-10
 */

public class EnumClassDeclaration extends ClassDeclaration {

    /**
     * store the program variables which represent the enum constants
     */
    private final List<IProgramVariable> constants = new ArrayList<>();

    public EnumClassDeclaration(PositionInfo pi, List<Comment> c, ImmutableArray<Modifier> modArray,
            ProgramElementName name, ProgramElementName fullName,
            ImmutableArray<MemberDeclaration> members, boolean parentIsInterface, boolean isLibrary,
            Extends extending, Implements implementing, ImmutableList<TextualJMLConstruct> spec,
            Sort sort) {
        super(pi, c, modArray, name, fullName, members, parentIsInterface, isLibrary, extending,
            implementing, false, false, false, spec);

        for (var m : members) {
            if (m instanceof FieldDeclaration fd && fd.isFinal() && fd.isStatic() && fd.isPublic()
                    && fd.getFieldSpecifications().size() == 1) {
                var fs = fd.getFieldSpecifications().get(0);
                if (fs.getProgramVariable().sort() == sort)
                    constants.add(fs.getProgramVariable());
            }
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
     */
    public static boolean isEnumConstant(IProgramVariable attribute) {
        KeYJavaType kjt = attribute.getKeYJavaType();
        Type type = kjt.getJavaType();
        if (type instanceof EnumClassDeclaration ecd) {
            return ecd.isLocalEnumConstant(attribute);
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

}
