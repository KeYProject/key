/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;

/**
 * This class is used by LogicPrinter.java to print out store-terms, i.e. terms of the following
 * form: store(heap, object, field, value)
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
class StorePrinter extends FieldPrinter {

    StorePrinter(Services services) {
        super(services);
    }

    /*
     * Common code for all pretty-printed store variants. This section is executed at the beginning
     * of pretty-printing.
     */
    private void initPrettyPrint(LogicPrinter lp, final Term heapTerm) {
        lp.layouter.startTerm(4);

        lp.layouter.markStartSub();
        boolean hasEmbedded = lp.printEmbeddedHeapConstructorTerm(heapTerm);
        lp.layouter.markEndSub();

        if (hasEmbedded) {
            lp.layouter.brk(0);
        } else {
            lp.layouter.beginC(0);
        }

        lp.layouter.print("[");
    }

    /*
     * Common code for all pretty-printed store variants. This section is executed at the end of
     * pretty-printing.
     */
    private void finishPrettyPrint(LogicPrinter lp, final Term valueTerm, boolean closingBrace) {
        lp.layouter.print(" := ");
        lp.layouter.markStartSub();
        lp.printTerm(valueTerm);
        lp.layouter.markEndSub();

        lp.layouter.print("]");

        if (closingBrace) {
            lp.layouter.end();
        }
    }

    void printStore(LogicPrinter lp, Term t, boolean closingBrace) {
        assert t.boundVars().isEmpty();
        assert t.arity() == 4;

        final HeapLDT heapLDT = lp.getHeapLDT();

        if (lp.notationInfo.isPrettySyntax() && heapLDT != null) {

            final Term heapTerm = t.sub(0);
            final Term objectTerm = t.sub(1);
            final Term fieldTerm = t.sub(2);
            final Term valueTerm = t.sub(3);

            if (isStaticFieldConstant(objectTerm, fieldTerm)) {
                printStoreOnStaticField(lp, heapTerm, fieldTerm, valueTerm, closingBrace);
            } else if (isBuiltinObjectProperty(fieldTerm)) {
                printStoreOnGenericFieldConstant(lp, heapTerm, objectTerm, fieldTerm, valueTerm,
                    closingBrace);
            } else if (isJavaFieldConstant(fieldTerm)) {
                printStoreOnJavaFieldConstant(lp, heapTerm, objectTerm, fieldTerm, valueTerm,
                    closingBrace);
            } else if (fieldTerm.op() == heapLDT.getArr()) {
                printStoreOnArrayElement(lp, heapTerm, objectTerm, fieldTerm, valueTerm,
                    closingBrace);
            } else {
                lp.printFunctionTerm(t);
            }
        } else {
            lp.printFunctionTerm(t);
        }
    }

    /*
     * This is called in case parameter fieldTerm represents an array element.
     */
    private void printStoreOnArrayElement(LogicPrinter lp, final Term heapTerm,
            final Term objectTerm,
            final Term fieldTerm, final Term valueTerm, boolean closingBrace) {
        initPrettyPrint(lp, heapTerm);

        PosTableLayouter layouter = lp.layouter();
        layouter.markStartSub();
        lp.printTerm(objectTerm);
        layouter.markEndSub();

        lp.layouter.print("[");

        layouter.markStartSub();
        layouter.startTerm(1);
        layouter.markStartSub();
        lp.printTerm(fieldTerm.sub(0));
        layouter.markEndSub();
        layouter.markEndSub();

        layouter.print("]");

        finishPrettyPrint(lp, valueTerm, closingBrace);
    }

    /*
     * This is called in case parameter fieldTerm represents a non-static field.
     */
    private void printStoreOnJavaFieldConstant(LogicPrinter lp, final Term heapTerm,
            final Term objectTerm,
            final Term fieldTerm, final Term valueTerm, boolean closingBrace) {
        initPrettyPrint(lp, heapTerm);

        lp.layouter.markStartSub();
        lp.printTerm(objectTerm);
        lp.layouter.markEndSub();

        lp.layouter.print(".");

        lp.layouter.markStartSub();
        lp.layouter.startTerm(0);
        lp.layouter.print(getPrettySyntaxForFieldConstant(objectTerm, fieldTerm));
        lp.printLabels(fieldTerm);
        lp.layouter.markEndSub();

        finishPrettyPrint(lp, valueTerm, closingBrace);
    }

    private void printStoreOnGenericFieldConstant(LogicPrinter lp, final Term heapTerm,
            final Term objectTerm,
            final Term fieldTerm, final Term valueTerm, boolean closingBrace) {
        initPrettyPrint(lp, heapTerm);

        lp.layouter.markStartSub();
        lp.printTerm(objectTerm);
        lp.layouter.markEndSub();

        lp.layouter.print(".");

        lp.layouter.markStartSub();
        lp.layouter.startTerm(0);
        lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
        lp.layouter.markEndSub();

        finishPrettyPrint(lp, valueTerm, closingBrace);
    }

    /*
     * This is called in case parameter fieldTerm represents a static field.
     */
    private void printStoreOnStaticField(LogicPrinter lp, final Term heapTerm, final Term fieldTerm,
            final Term valueTerm, boolean closingBrace) {
        initPrettyPrint(lp, heapTerm);

        String className = HeapLDT.getClassName((Function) fieldTerm.op());

        if (className == null) {
            lp.layouter.markStartSub();
            lp.printTerm(services.getTermBuilder().NULL());
            lp.layouter.markEndSub();
        } else {
            lp.layouter.markStartSub();
            // "null" not printed
            lp.layouter.markEndSub();
            lp.printClassName(className);
        }

        lp.layouter.print(".");

        lp.layouter.markStartSub();
        lp.layouter.startTerm(0);
        lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
        lp.layouter.markEndSub();

        finishPrettyPrint(lp, valueTerm, closingBrace);
    }

}
