/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.util.NoSuchElementException;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NonNull;

/**
 * Common superclass of {@link StorePrinter} and {@link SelectPrinter}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
class FieldPrinter {

    // protected final LogicPrinter lp;
    protected final Services services;

    FieldPrinter(Services services) {
        this.services = services;
    }

    /**
     * Determine the syntax in which a field constant is printed when associated with the object
     * represented by {@code objectTerm} Default is the name of the field. In case the field is
     * hidden by another field, the name of the field is preceeded by the corresponding class name.
     *
     * Example default: object.field Example hidden field: object.(package.class::field)
     */
    protected String getPrettySyntaxForFieldConstant(JTerm objectTerm, JTerm fieldTerm) {
        JavaInfo javaInfo = services.getJavaInfo();

        if (isCanonicField(objectTerm, fieldTerm, javaInfo)) {
            /*
             * Class name can be omitted if the field is canonic, i.e. correct field can be
             * determined without explicit mentioning of corresponding class name.
             *
             * Example syntax: object.field
             */
            return HeapLDT.getPrettyFieldName(fieldTerm.op());
        } else {
            /*
             * There is another field of the same name that would be selected if class name is
             * omitted. In this case class name must be mentioned explicitly.
             *
             * Example syntax: object.(package.class::field)
             */
            return "(" + fieldTerm.op().toString().replace("::$", "::") + ")";
        }
    }

    /*
     * Determine whether class can be omitted when printing a field in a select term. A field can be
     * omitted, if it is canonic for the associated object.
     *
     * For more information on canonic, see {@link
     * de.uka.ilkd.key.java.JavaInfo#getCanonicalFieldProgramVariable(String,KeYJavaType)}
     *
     * (Kai Wallisch 09/2014)
     */
    private boolean isCanonicField(JTerm objectTerm, JTerm fieldTerm, JavaInfo javaInfo) {
        Sort sort = objectTerm.sort();
        KeYJavaType kjt = javaInfo.getKeYJavaType(sort);
        String fieldName = HeapLDT.getPrettyFieldName(fieldTerm.op());
        ProgramVariable pv = javaInfo.getCanonicalFieldProgramVariable(fieldName, kjt);
        if (pv == null) {
            return false;
        }

        /*
         * Compare originTypeAndName and pvTypeAndName based on their String representation. I did
         * not find a better solution to this yet. But it seems to be standard, as it is done
         * similary in method HeapLDT.getPrettyFieldName(). (Kai Wallisch 09/2014)
         */
        String[] originTypeAndName = fieldTerm.toString().split("::\\$");
        assert originTypeAndName.length == 2;
        String[] pvTypeAndName = pv.toString().split("::");
        assert pvTypeAndName.length == 2;

        return (pvTypeAndName[0].equals(originTypeAndName[0])
                && pvTypeAndName[1].equals(originTypeAndName[1]));
    }

    /*
     * Determine whether a term is a constant function symbol of type field.
     */
    protected static boolean isFieldConstant(JTerm fieldTerm, HeapLDT heapLDT) {
        return fieldTerm.op() instanceof Function && ((Function) fieldTerm.op()).isUnique()
                && fieldTerm.sort() == heapLDT.getFieldSort() && fieldTerm.arity() == 0
                && fieldTerm.boundVars().isEmpty();
    }

    /**
     * Find the attribute program variable for a field term.
     *
     * @return Returns the attribute program variable for the given field term.
     * @param fieldTerm The field term to analyse.
     */
    protected static @NonNull ProgramVariable getJavaFieldConstant(JTerm fieldTerm, HeapLDT heapLDT,
            Services services) {
        String name = fieldTerm.op().name().toString();
        if (name.contains("::$") && isFieldConstant(fieldTerm, heapLDT)) {
            String pvName = name.replace("::$", "::");
            ProgramVariable result = services.getJavaInfo().getAttribute(pvName);
            if (result == null) {
                throw new NoSuchElementException("No field constant: " + fieldTerm);
            }
            return result;
        }
        throw new IllegalArgumentException("No field constant: " + fieldTerm);
    }

    /**
     * Find out whether a {@link JTerm} represents a field symbol, declared in a Java class.
     *
     * @return Returns true iff the given parameter represents a field constant.
     * @param fieldTerm The target field.
     */
    protected static boolean isJavaFieldConstant(JTerm fieldTerm, HeapLDT heapLDT,
            Services services) {
        try {
            // the called method either returns a ProgramVariable or throws an exception
            // We are only interested in whether the method throws an exception or not, so we
            // ignore the return value.
            getJavaFieldConstant(fieldTerm, heapLDT, services);
            return true;
        } catch (RuntimeException e) {
            // If there exists a constant of the form x::$y and there is no type
            // x, this exception is thrown.
            return false;
        }
    }

    protected boolean isJavaFieldConstant(JTerm fieldTerm) {
        return isJavaFieldConstant(fieldTerm, services.getTypeConverter().getHeapLDT(), services);
    }

    /*
     * Determine whether the field constant is a generic object property. Those are surrounded by
     * angle brackets, e.g. o.<created>
     */
    protected boolean isBuiltinObjectProperty(JTerm fieldTerm) {
        return fieldTerm.op().name().toString().contains("::<")
                && isFieldConstant(fieldTerm, services.getTypeConverter().getHeapLDT());
    }

    /*
     * Determine whether a field constant is static.
     */
    protected boolean isStaticFieldConstant(JTerm fieldTerm) {
        try {
            ProgramVariable pv =
                getJavaFieldConstant(fieldTerm, services.getTypeConverter().getHeapLDT(), services);
            return pv.isStatic();
        } catch (RuntimeException e) {
            return false;
        }
    }

    /*
     * Determine whether a field constant is declared final.
     */
    protected boolean isFinalFieldConstant(JTerm fieldTerm) {
        try {
            ProgramVariable pv =
                getJavaFieldConstant(fieldTerm, services.getTypeConverter().getHeapLDT(), services);
            return pv.isFinal();
        } catch (RuntimeException e) {
            return false;
        }
    }

}
