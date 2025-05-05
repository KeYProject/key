/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;


import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;

/**
 * This class is used by LogicPrinter.java to print out final-terms, i.e. terms
 * of the following form: T::final(heap, object, field)
 *
 * Almost exact copy of SelectPrinter without the heap printing.
 *
 * @author Julian Wiesler <wiesleju@gmail.com>
 */
class FinalPrinter extends FieldPrinter {

    FinalPrinter(Services services) {
        super(services);
    }

    /*
     * Print a term of the form: T::final(object, field).
     */
    public void printFinal(LogicPrinter lp, Term t) {
        assert t.boundVars().isEmpty();
        assert t.arity() == 2;
        HeapLDT heapLDT = lp.getHeapLDT();

        if (lp.notationInfo.isPrettySyntax() && heapLDT != null) {
            final Term objectTerm = t.sub(0);
            final Term fieldTerm = t.sub(1);
            // Array selects are never final, no need to handle them
            if (t.sort().equals(JavaDLTheory.ANY)) {
                /*
                 * This section deals with PP of frame conditions (and similar).
                 * Select-type is any.
                 */
                // if (isFieldName(fieldTerm.op().name().toString(), objectTerm)
                // || isJavaFieldConstant(fieldTerm)) {
                lp.printFunctionTerm(t);
                // } else {
                // printAnySelect(lp, objectTerm, fieldTerm);
                // }
            } else if (isBuiltinObjectProperty(fieldTerm)) {
                // object properties denoted like o.<created>
                printBuiltinObjectProperty(lp, t, objectTerm, fieldTerm);
            } else if (isStaticFieldConstant(fieldTerm)
                    && getFieldSort(fieldTerm).equals(t.sort())) {
                // static field access
                printStaticJavaFieldConstant(lp, fieldTerm);
            } else if (isJavaFieldConstant(fieldTerm)
                    && isFinalFieldConstant(fieldTerm)
                    && getFieldSort(fieldTerm).equals(t.sort())) {
                // non-static field access to a final field
                printNonStaticJavaFieldConstant(lp, objectTerm, fieldTerm);
            } else {
                lp.printFunctionTerm(t);
            }
        } else {
            lp.printFunctionTerm(t);
        }
    }

    /*
     * Check whether there is a field with the same name as a variable.
     */
    private boolean isFieldName(String variableName, Term objectTerm) {
        Sort sort = objectTerm.sort();
        JavaInfo javaInfo = services.getJavaInfo();
        KeYJavaType kjt = javaInfo.getKeYJavaType(sort);
        ProgramVariable pv = javaInfo.getCanonicalFieldProgramVariable(variableName, kjt);
        return pv != null;
    }

    /*
     * Get sort of selected field.
     */
    private Sort getFieldSort(Term fieldTerm) {
        String lookup = fieldTerm.op().toString().replace("$", "");
        ProgramVariable progVar = services.getJavaInfo().getAttribute(lookup);
        return progVar.sort();
    }

    /*
     * Print a static field constant.
     */
    private void printStaticJavaFieldConstant(
            LogicPrinter lp, final Term fieldTerm) {
        lp.layouter.startTerm(2);
        /*
         * Is consideration for static arrays missing in this?
         * (Kai Wallisch 08/2014)
         *
         * No, array accesses are not static selects.
         * This only handles the access to the static array reference.
         */

        String className = HeapLDT.getClassName((Function) fieldTerm.op());

        if (className == null) {
            // if the class name cannot be determined, print "null"
            lp.layouter.markStartSub(0);
            lp.printTerm(lp.services.getTermBuilder().NULL());
            lp.layouter.markEndSub();
        } else {
            lp.layouter.markStartSub(0);
            // "null" not printed, print className (which is not a subterm)
            lp.layouter.markEndSub();
            lp.printClassName(className);
        }

        lp.layouter.print(".");
        lp.layouter.markStartSub(1);
        lp.layouter.startTerm(0);
        lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
        lp.layouter.markEndSub();
    }

    /*
     * Print a non-static field constant.
     */
    private void printNonStaticJavaFieldConstant(
            LogicPrinter lp, final Term objectTerm,
            final Term fieldTerm) {
        lp.layouter.startTerm(2);
        lp.layouter.markStartSub(0);
        lp.printTerm(objectTerm);
        lp.layouter.markEndSub();
        lp.layouter.print(".");
        lp.layouter.markStartSub(1);
        lp.layouter.startTerm(0);
        lp.layouter.print(getPrettySyntaxForFieldConstant(objectTerm, fieldTerm));
        lp.printLabels(fieldTerm);
        lp.layouter.markEndSub();
    }

    /*
     * Print a term of the form: any::final(heap, object, field).
     */
    private void printAnySelect(
            LogicPrinter lp, final Term objectTerm,
            final Term fieldTerm) {
        lp.layouter.startTerm(2);
        lp.layouter.markStartSub(0);
        lp.printTerm(objectTerm);
        lp.layouter.markEndSub();
        lp.layouter.print(".");
        lp.layouter.markStartSub(1);
        lp.printTerm(fieldTerm);
        lp.layouter.markEndSub();
    }

    /*
     * Print a select-term of the following form:
     * T::final( ... , ... , java.lang.Object::<...>)
     * For example:
     * boolean::final(heap, object, java.lang.Object::<created>)
     */
    private void printBuiltinObjectProperty(
            LogicPrinter lp, Term t,
            Term objectTerm,
            Term fieldTerm) {
        JavaInfo javaInfo = services.getJavaInfo();
        KeYJavaType selectKJT = javaInfo.getKeYJavaType(t.sort());
        KeYJavaType objectKJT = javaInfo.getKeYJavaType(objectTerm.sort());

        if (selectKJT != null && objectKJT != null) {
            assert fieldTerm.op().name().toString().contains("::<");
            String prettyFieldName = HeapLDT.getPrettyFieldName(fieldTerm.op());
            ProgramVariable pv =
                javaInfo.getCanonicalFieldProgramVariable(prettyFieldName, objectKJT);

            if (pv != null && pv.sort().equals(t.sort())) {
                lp.layouter.startTerm(2);
                lp.layouter.markStartSub(0);
                lp.printTerm(objectTerm);
                lp.layouter.markEndSub();
                lp.layouter.print(".");
                lp.layouter.markStartSub(1);
                lp.printConstant(fieldTerm, prettyFieldName);
                lp.layouter.markEndSub();
            } else {
                // In case field sort is not equal to select sort, use generic fallback.
                lp.printFunctionTerm(t);
            }

        } else {
            // In case select sort is no KeYJavaType, use generic fallback.
            lp.printFunctionTerm(t);
        }
    }

}
