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
class StorePrinter {

    private final LogicPrinter lp;

    StorePrinter(LogicPrinter lp) {
        this.lp = lp;
    }

    void printStore(Term t, boolean closingBrace) throws IOException {
        assert t.boundVars().isEmpty();
        assert t.arity() == 4;

        final HeapLDT heapLDT = lp.getHeapLDT();

        if (lp.notationInfo.isPrettySyntax() && heapLDT != null) {
            lp.startTerm(4);

            final Term heapTerm = t.sub(0);
            final Term objectTerm = t.sub(1);
            final Term fieldTerm = t.sub(2);
            final Term valueTerm = t.sub(3);

            lp.markStartSub();
            boolean hasEmbedded = lp.printEmbeddedHeapConstructorTerm(heapTerm);
            lp.markEndSub();

            if (hasEmbedded) {
                lp.layouter.brk(0);
            } else {
                lp.layouter.beginC(0);
            }

            lp.layouter.print("[");

            if (objectTerm.equals(lp.services.getTermBuilder().NULL())
                    && fieldTerm.op() instanceof Function
                    && ((Function) fieldTerm.op()).isUnique()) {

                String className = HeapLDT.getClassName((Function) fieldTerm.op());

                if (className == null) {
                    lp.markStartSub();
                    lp.printTerm(objectTerm);
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
                lp.printTerm(fieldTerm);
                lp.markEndSub();
            } else if (fieldTerm.arity() == 0) {
                lp.markStartSub();
                lp.printTerm(objectTerm);
                lp.markEndSub();

                lp.layouter.print(".");

                lp.markStartSub();
                lp.startTerm(0);

                /* TODO: More sophisticated determination of pretty-syntax, similar
                 * to select-syntax. Using HeapLDT.getPrettySyntax() here for now,
                 * as it is current behaviour for KeY.
                 *
                 * (Kai Wallisch 09/2014)
                 */
                lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
                lp.markEndSub();
            } else if (fieldTerm.op() == heapLDT.getArr()) {
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
            } else {
                lp.printFunctionTerm(t);
            }

            lp.layouter.print(" := ");
            lp.markStartSub();
            lp.printTerm(valueTerm);
            lp.markEndSub();

            lp.layouter.print("]");

            if (closingBrace) {
                lp.layouter.end();
            }

        } else {
            /*
             * TODO: This is misplaced, since store-term is already partially
             * printed at this point. Needs refactoring.
             * (Kai Wallisch 09/2014)
             */
            lp.printFunctionTerm(t);
        }
    }

}
