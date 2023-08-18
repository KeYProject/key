/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class is used by LogicPrinter.java to print out select-terms, i.e. terms of the following
 * form: T::select(heap, object, field)
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
class SelectPrinter extends FieldPrinter {

    SelectPrinter(Services services) {
        super(services);
    }

    /*
     * Print a term of the form: T::select(heap, object, field).
     */
    public void printSelect(LogicPrinter lp, Term t, Term tacitHeap) {
        assert t.boundVars().isEmpty();
        assert t.arity() == 3;
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        if (lp.notationInfo.isPrettySyntax() && heapLDT != null) {

            // if tacitHeap is null, use default heap as tacitHeap
            if (tacitHeap == null) {
                tacitHeap = services.getTermFactory().createTerm(heapLDT.getHeap());
            }

            final Term heapTerm = t.sub(0);
            final Term objectTerm = t.sub(1);
            final Term fieldTerm = t.sub(2);
            if (fieldTerm.op() == heapLDT.getArr()) {
                KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(objectTerm.sort());
                Type jtype = null;
                if (kjt != null) {
                    jtype = kjt.getJavaType();
                }
                if (jtype instanceof ArrayType && ((ArrayType) jtype).getBaseType().getKeYJavaType()
                        .getSort() == t.sort()) {
                    printArraySelect(lp, heapTerm, objectTerm, fieldTerm, tacitHeap);
                } else {
                    lp.printFunctionTerm(t);
                }
            } else if (t.sort().equals(Sort.ANY)) {
                /*
                 * This section deals with PP of frame conditions (and similar). Select-type is any.
                 */
                if (isFieldName(fieldTerm.op().name().toString(), objectTerm)
                        || isJavaFieldConstant(fieldTerm)) {
                    lp.printFunctionTerm(t);
                } else {
                    printAnySelect(lp, heapTerm, objectTerm, fieldTerm, tacitHeap);
                }
            } else if (isBuiltinObjectProperty(fieldTerm)) {
                // object properties denoted like o.<created>
                printBuiltinObjectProperty(lp, t, heapTerm, objectTerm, fieldTerm, tacitHeap);
            } else if (isStaticFieldConstant(objectTerm, fieldTerm)
                    && getFieldSort(fieldTerm).equals(t.sort())) {
                // static field access
                printStaticJavaFieldConstant(lp, fieldTerm, heapTerm, tacitHeap);
            } else if (isJavaFieldConstant(fieldTerm) && getFieldSort(fieldTerm).equals(t.sort())) {
                // non-static field access
                printNonStaticJavaFieldConstant(lp, heapTerm, objectTerm, fieldTerm, tacitHeap);
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
     * Add heap term after a pretty-printed select, using @-Operator.
     */
    private void printHeap(LogicPrinter lp, Term heapTerm, Term tacitHeap) {
        // print heap term if it is not the standard heap
        if (!heapTerm.equals(tacitHeap)) {
            lp.layouter./* brk(1, -3). */print("@");
            lp.layouter.markStartSub(0);
            // if, one day, there are infix heap expressions, this needs to be
            // maybeParens(...):
            lp.printTerm(heapTerm);
            lp.layouter.markEndSub();
        } else {
            // heap not printed
            lp.layouter.markStartSub(0);
            lp.layouter.markEndSub();
        }
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
    private void printStaticJavaFieldConstant(LogicPrinter lp, final Term fieldTerm,
            final Term heapTerm,
            Term tacitHeap) {
        lp.layouter.startTerm(3);
        /*
         * Is consideration for static arrays missing in this? (Kai Wallisch 08/2014)
         */

        String className = HeapLDT.getClassName((Function) fieldTerm.op());

        if (className == null) {
            // if the class name cannot be determined, print "null"
            lp.layouter.markStartSub(1);
            lp.printTerm(services.getTermBuilder().NULL());
            lp.layouter.markEndSub();
        } else {
            lp.layouter.markStartSub(1);
            // "null" not printed, print className (which is not a subterm)
            lp.layouter.markEndSub();
            lp.printClassName(className);
        }

        lp.layouter.print(".");
        lp.layouter.markStartSub(2);
        lp.layouter.startTerm(0);
        lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
        lp.layouter.markEndSub();

        printHeap(lp, heapTerm, tacitHeap);
    }

    /*
     * Print a non-static field constant.
     */
    private void printNonStaticJavaFieldConstant(LogicPrinter printer, final Term heapTerm,
            final Term objectTerm,
            final Term fieldTerm, Term tacitHeap) {
        printer.layouter.startTerm(3);
        printer.layouter.markStartSub(1);
        printer.printEmbeddedObserver(heapTerm, objectTerm);
        printer.layouter.markEndSub();
        printer.layouter.print(".");
        printer.layouter.markStartSub(2);
        printer.layouter.startTerm(0);
        printer.layouter.print(getPrettySyntaxForFieldConstant(objectTerm, fieldTerm));
        printer.printLabels(fieldTerm);
        printer.layouter.markEndSub();
        printHeap(printer, heapTerm, tacitHeap);
    }

    /*
     * Print a term of the form: any::select(heap, object, field).
     */
    private void printAnySelect(LogicPrinter lp, final Term heapTerm, final Term objectTerm,
            final Term fieldTerm,
            Term tacitHeap) {
        lp.layouter.startTerm(3);
        lp.layouter.markStartSub(1);
        lp.printEmbeddedObserver(heapTerm, objectTerm);
        lp.layouter.markEndSub();
        lp.layouter.print(".");
        lp.layouter.markStartSub(2);
        lp.printTerm(fieldTerm);
        lp.layouter.markEndSub();
        printHeap(lp, heapTerm, tacitHeap);
    }

    /*
     * Print out a select on an array.
     */
    private void printArraySelect(LogicPrinter lp, Term heapTerm, Term objectTerm, Term fieldTerm,
            Term tacitHeap) {

        lp.layouter.startTerm(3);
        lp.layouter.markStartSub(1);
        lp.printEmbeddedObserver(heapTerm, objectTerm);
        lp.layouter.markEndSub();

        lp.layouter.print("[");
        lp.layouter.markStartSub(2);

        /*
         * Used to be startTerm(2). Changed it to startTerm(1) because array has only 1 argument.
         * (Kai Wallisch 09/2014)
         */
        lp.layouter.startTerm(1);
        lp.layouter.markStartSub();
        lp.printTerm(fieldTerm.sub(0));
        lp.layouter.markEndSub();
        lp.layouter.markEndSub();
        lp.layouter.print("]");

        printHeap(lp, heapTerm, tacitHeap);
    }

    /*
     * Print a select-term of the following form: T::select( ... , ... , java.lang.Object::<...>)
     * For example: boolean::select(heap, object, java.lang.Object::<created>)
     */
    private void printBuiltinObjectProperty(LogicPrinter lp, Term t, Term heapTerm, Term objectTerm,
            Term fieldTerm,
            Term tacitHeap) {

        JavaInfo javaInfo = services.getJavaInfo();
        KeYJavaType selectKJT = javaInfo.getKeYJavaType(t.sort());
        KeYJavaType objectKJT = javaInfo.getKeYJavaType(objectTerm.sort());

        if (selectKJT != null && objectKJT != null) {

            assert fieldTerm.op().name().toString().contains("::<");
            String prettyFieldName = HeapLDT.getPrettyFieldName(fieldTerm.op());
            ProgramVariable pv =
                javaInfo.getCanonicalFieldProgramVariable(prettyFieldName, objectKJT);

            if (pv != null && pv.sort().equals(t.sort())) {
                lp.layouter.startTerm(3);
                lp.layouter.markStartSub(1);
                lp.printEmbeddedObserver(heapTerm, objectTerm);
                lp.layouter.markEndSub();
                lp.layouter.print(".");
                lp.layouter.markStartSub(2);
                lp.printConstant(fieldTerm, prettyFieldName);
                lp.layouter.markEndSub();
                printHeap(lp, heapTerm, tacitHeap);
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
