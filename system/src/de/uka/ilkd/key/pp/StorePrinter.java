package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import java.io.IOException;

/**
 * This class is used by LogicPrinter.java to print out store-terms, i.e. terms
 * of the following form: store(heap, object, field, value)
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
class StorePrinter extends FieldPrinter {

    StorePrinter(LogicPrinter lp) {
        super(lp);
    }

    /*
     * Common code for all pretty-printed store variants.
     * This section is executed at the beginning of pretty-printing.
     */
    private void initPrettyPrint(final Term heapTerm) throws IOException {
        lp.startTerm(4);

        lp.markStartSub();
        boolean hasEmbedded = lp.printEmbeddedHeapConstructorTerm(heapTerm);
        lp.markEndSub();

        if (hasEmbedded) {
            lp.layouter.brk(0);
        } else {
            lp.layouter.beginC(0);
        }

        lp.layouter.print("[");
    }

    /*
     * Common code for all pretty-printed store variants.
     * This section is executed at the end of pretty-printing.
     */
    private void finishPrettyPrint(final Term valueTerm, boolean closingBrace) throws IOException {
        lp.layouter.print(" := ");
        lp.markStartSub();
        lp.printTerm(valueTerm);
        lp.markEndSub();

        lp.layouter.print("]");

        if (closingBrace) {
            lp.layouter.end();
        }
    }

    void printStore(Term t, boolean closingBrace) throws IOException {
        assert t.boundVars().isEmpty();
        assert t.arity() == 4;

        final HeapLDT heapLDT = lp.getHeapLDT();

        if (lp.notationInfo.isPrettySyntax() && heapLDT != null) {

            final Term heapTerm = t.sub(0);
            final Term objectTerm = t.sub(1);
            final Term fieldTerm = t.sub(2);
            final Term valueTerm = t.sub(3);

            if (isStaticFieldConstant(objectTerm, fieldTerm)) {
                printStoreOnStaticField(heapTerm, fieldTerm, valueTerm, closingBrace);
            } else if (isGenericFieldConstant(fieldTerm)) {
                printStoreOnGenericFieldConstant(heapTerm, objectTerm, fieldTerm, valueTerm, closingBrace);
            } else if (isJavaFieldConstant(fieldTerm)) {
                printStoreOnJavaFieldConstant(heapTerm, objectTerm, fieldTerm, valueTerm, closingBrace);
            } else if (fieldTerm.op() == heapLDT.getArr()) {
                printStoreOnArrayElement(heapTerm, objectTerm, fieldTerm, valueTerm, closingBrace);
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
    private void printStoreOnArrayElement(final Term heapTerm, final Term objectTerm, final Term fieldTerm, final Term valueTerm, boolean closingBrace) throws IOException {
        initPrettyPrint(heapTerm);

        lp.markStartSub();
        lp.printTerm(objectTerm);
        lp.markEndSub();

        lp.layouter.print("[");

        lp.markStartSub();
        lp.startTerm(1);
        lp.markStartSub();
        lp.printTerm(fieldTerm.sub(0));
        lp.markEndSub();
        lp.markEndSub();

        lp.layouter.print("]");

        finishPrettyPrint(valueTerm, closingBrace);
    }

    /*
     * This is called in case parameter fieldTerm represents a non-static field.
     */
    private void printStoreOnJavaFieldConstant(final Term heapTerm, final Term objectTerm, final Term fieldTerm, final Term valueTerm, boolean closingBrace) throws IOException {
        initPrettyPrint(heapTerm);

        lp.markStartSub();
        lp.printTerm(objectTerm);
        lp.markEndSub();

        lp.layouter.print(".");

        lp.markStartSub();
        lp.startTerm(0);
        lp.layouter.print(getPrettySyntaxForFieldConstant(objectTerm, fieldTerm));
        lp.markEndSub();

        finishPrettyPrint(valueTerm, closingBrace);
    }

    private void printStoreOnGenericFieldConstant(final Term heapTerm, final Term objectTerm, final Term fieldTerm, final Term valueTerm, boolean closingBrace) throws IOException {
        initPrettyPrint(heapTerm);

        lp.markStartSub();
        lp.printTerm(objectTerm);
        lp.markEndSub();

        lp.layouter.print(".");

        lp.markStartSub();
        lp.startTerm(0);
        lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
        lp.markEndSub();

        finishPrettyPrint(valueTerm, closingBrace);
    }

    /*
     * This is called in case parameter fieldTerm represents a static field.
     */
    private void printStoreOnStaticField(final Term heapTerm, final Term fieldTerm, final Term valueTerm, boolean closingBrace) throws IOException {
        initPrettyPrint(heapTerm);

        String className = HeapLDT.getClassName((Function) fieldTerm.op());

        if (className == null) {
            lp.markStartSub();
            lp.printTerm(lp.services.getTermBuilder().NULL());
            lp.markEndSub();
        } else {
            lp.markStartSub();
            // "null" not printed
            lp.markEndSub();
            lp.printClassName(className);
        }

        lp.layouter.print(".");

        lp.markStartSub();
        lp.startTerm(0);
        lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
        lp.markEndSub();

        finishPrettyPrint(valueTerm, closingBrace);
    }

}
