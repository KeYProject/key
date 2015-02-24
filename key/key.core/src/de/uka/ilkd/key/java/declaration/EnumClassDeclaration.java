// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.declaration;

import java.util.ArrayList;
import java.util.List;

import recoder.java.declaration.EnumConstantDeclaration;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.ExtList;

/**
 * This class is used for wrapping an enum into a standard class type.
 * 
 * <p>In addition the programvariables that represent enum constants are memorized. Thus
 * this class is able to have queries on the enum constants. 
 * 
 * @author mulbrich
 * @since 2006-12-10
 */

public class EnumClassDeclaration extends ClassDeclaration {

    /**
     * store the program variables which represent the enum constants
     */
    private List<IProgramVariable> constants = new ArrayList<IProgramVariable>();

    /**
     * create a new EnumClassDeclaration that describes an enum defintion. It
     * merely wraps a ClassDeclaration but has memory about which fields have
     * been declared as enum constants.
     * 
     * @param children
     *            children in the ast (members)
     * @param fullName
     *            of the class/enum
     * @param isLibrary
     *            see class constructor
     * @param enumConstantDeclarations
     *            the declarations for the enum constants
     */
    public EnumClassDeclaration(ExtList children, ProgramElementName fullName,
            boolean isLibrary,
            List<EnumConstantDeclaration> enumConstantDeclarations) {

        super(children, fullName, isLibrary);

        for (EnumConstantDeclaration ecd : enumConstantDeclarations) {
            String constName = ecd.getEnumConstantSpecification().getName();
            constants.add(findAttr(constName));
        }
    }

    /*
     * find the program variable for a constant given by name.
     * 
     * The "<Name>::" have to be prepended to obtain the internal name.
     * Throw IllegalStateException if name is not an attribute of this.
     * This will never happen.
     * 
     */
    private IProgramVariable findAttr(String fieldName) {
        String completeName = getFullName() + "::" + fieldName;
        for (int i = 0; i < members.size(); i++) {
            if (members.get(i) instanceof FieldDeclaration) {
                FieldDeclaration fd = (FieldDeclaration) members.get(i);
                FieldSpecification fs = fd.getFieldSpecifications().get(0);
                if (fs.getName().equals(completeName)) {
                    return fs.getProgramVariable();
                }
            }
        }
        throw new IllegalStateException(fieldName + " is not an attribute of "
                + this.getFullName());
    }

    /*
     * is pv a enum constant of THIS enum?
     */
    private boolean isLocalEnumConstant(IProgramVariable pv) {
        for (IProgramVariable cnst : constants) {
            if (cnst.equals(pv))
                return true;
        }
        return false;
    }

    /**
     * get the index of the program variable amongst the enumconstants of THIS enum.
     * @param pv PV to look up
     * @return -1 if not found, otherwise the 0-based index.
     */
    private int localIndexOf(ProgramVariable pv) {
        for (int i = 0; i < constants.size(); i++) {
            if (constants.get(i).equals(pv))
                return i;
        }
        return -1;
    }

    /**
     * get the number of defined enum constants in this type.
     * @return the number of defined enum constants in this type
     */
    public int getNumberOfConstants() {
        return constants.size();
    }

    /**
     * check whether a PV is an enum constant of any enum type.
     * @param attribute ProgramVariable to check.
     * @return true iff attribute is an enum constant.
     */
    public static boolean isEnumConstant(IProgramVariable attribute) {
        KeYJavaType kjt = attribute.getKeYJavaType();
        Type type = kjt.getJavaType();
        if (type instanceof EnumClassDeclaration)
            return ((EnumClassDeclaration) type).isLocalEnumConstant(attribute);
        else
            return false;
    }
    
    // TODO DOC
    public static int indexOf(ProgramVariable attribute) {
        KeYJavaType kjt = attribute.getKeYJavaType();
        Type type = kjt.getJavaType();
        if (type instanceof EnumClassDeclaration)
            return ((EnumClassDeclaration) type).localIndexOf(attribute);
        else
            return -1;
    }

}