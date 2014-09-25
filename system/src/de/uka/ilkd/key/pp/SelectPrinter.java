package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import java.io.IOException;

/**
 * This class is used by LogicPrinter.java to print out select-terms, i.e. terms
 * of the following form: T::select(heap, object, field)
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
class SelectPrinter {

    private final LogicPrinter lp;

    SelectPrinter(LogicPrinter lp) {
        this.lp = lp;
    }

    /*
     * Print a term of the form: T::select(heap, object, field).
     */
    public void printSelect(Term t, Term tacitHeap) throws IOException {
        assert t.boundVars().isEmpty();
        assert t.arity() == 3;
        HeapLDT heapLDT = lp.services == null ? null : lp.services.getTypeConverter().getHeapLDT();

        if (lp.notationInfo.isPrettySyntax() && heapLDT != null) {

            // if tacitHeap is null, use default heap as tacitHeap
            if (tacitHeap == null) {
                tacitHeap = lp.services.getTermFactory().createTerm(heapLDT.getHeap());
            }

            final Term heapTerm = t.sub(0);
            final Term objectTerm = t.sub(1);
            final Term fieldTerm = t.sub(2);

            if (t.sort().equals(Sort.ANY)) {
                /*
                 * This section deals with PP of frame conditions (and similar).
                 * Select-type is any.
                 */
                if (isFieldName(fieldTerm.op().toString(), objectTerm)
                        || lp.isFieldConstant(fieldTerm)) {
                    lp.printFunctionTerm(t);
                } else {
                    printAnySelect(heapTerm, objectTerm, fieldTerm, tacitHeap);
                }
            } else if (fieldTerm.op() == heapLDT.getArr()) {
                // array access
                printArraySelect(heapTerm, objectTerm, fieldTerm, tacitHeap);
            } else if (isSelectOnCreated(fieldTerm, t.sort())) {
                printCreated(heapTerm, objectTerm, tacitHeap);
            } else if (lp.isFieldConstant(fieldTerm) && getFieldSort(fieldTerm).equals(t.sort())) {
                printFieldConstantSelect(objectTerm, fieldTerm, heapLDT, heapTerm, tacitHeap);
            } else {
                lp.printFunctionTerm(t);
            }
        } else {
            lp.printFunctionTerm(t);
        }
    }

    /*
     * Determine whether class can be omitted when printing a field
     * in a select term. A field can be omitted, if it is canonic for
     * the associated object.
     * 
     * For more information on canonic, see
     * {@link de.uka.ilkd.key.java.JavaInfo#getCanonicalFieldProgramVariable(String,KeYJavaType)}
     * 
     * (Kai Wallisch 09/2014)
     */
    private boolean isCanonicField(Term objectTerm, Term fieldTerm) {
        Sort sort = objectTerm.sort();
        JavaInfo javaInfo = lp.services.getJavaInfo();
        KeYJavaType kjt = javaInfo.getKeYJavaType(sort);
        String fieldName = HeapLDT.getPrettyFieldName(fieldTerm.op());
        ProgramVariable pv = javaInfo.getCanonicalFieldProgramVariable(fieldName, kjt);
        if (pv == null) {
            return false;
        }

        /*
         * Compare originTypeAndName and pvTypeAndName based on their String
         * representation. I did not find a better solution to this yet.
         * But it seems to be standard, as it is done similary in method HeapLDT.getPrettyFieldName().
         * (Kai Wallisch 09/2014)
         */
        String[] originTypeAndName = fieldTerm.toString().split("::\\$");
        assert originTypeAndName.length == 2;
        String[] pvTypeAndName = pv.toString().split("::");
        assert pvTypeAndName.length == 2;

        return (pvTypeAndName[0].equals(originTypeAndName[0])
                && pvTypeAndName[1].equals(originTypeAndName[1]));
    }

    /*
     * Check whether there is a field with the same name as a variable.
     */
    private boolean isFieldName(String variableName, Term objectTerm) {
        Sort sort = objectTerm.sort();
        JavaInfo javaInfo = lp.services.getJavaInfo();
        KeYJavaType kjt = javaInfo.getKeYJavaType(sort);
        ProgramVariable pv = javaInfo.getCanonicalFieldProgramVariable(variableName, kjt);
        return pv != null;
    }

    /*
     * Add heap term after a pretty-printed select, using @-Operator.
     */
    private void printHeap(Term heapTerm, Term tacitHeap) throws IOException {
        // print heap term if it is not the standard heap
        if (!heapTerm.equals(tacitHeap)) {
            lp.layouter./*brk(1, -3).*/print("@");
            lp.markStartSub(0);
            // if, one day, there are infix heap expressions, this needs to be
            // maybeParens(...):
            lp.printTerm(heapTerm);
            lp.markEndSub();
        } else {
            // heap not printed
            lp.markStartSub(0);
            lp.markEndSub();
        }
    }

    /*
     * Get sort of selected field.
     */
    private Sort getFieldSort(Term fieldTerm) {
        String lookup = fieldTerm.toString().replace("$", "");
        ProgramVariable progVar = lp.services.getJavaInfo().getAttribute(lookup);
        return progVar.sort();
    }

    /*
     * Print a select on a field constant.
     */
    private void printFieldConstantSelect(final Term objectTerm, final Term fieldTerm, HeapLDT heapLDT, final Term heapTerm, Term tacitHeap) throws IOException {
        if (objectTerm.equals(lp.services.getTermBuilder().NULL())) {
            // static field access
            lp.startTerm(3);
            /*
             * Is consideration for static arrays missing in this?
             * (Kai Wallisch 08/2014)
             */

            String className = heapLDT.getClassName((Function) fieldTerm.op());

            if (className == null) {
                // if the class name cannot be determined, print "null"
                lp.markStartSub(1);
                lp.printTerm(lp.services.getTermBuilder().NULL());
                lp.markEndSub();
            } else {
                lp.markStartSub(1);
                // "null" not printed, print className (which is not a subterm)
                lp.markEndSub();
                lp.printClassName(className);
            }

            lp.layouter.print(".");
            lp.markStartSub(2);
            lp.printTerm(fieldTerm);
            lp.markEndSub();

            printHeap(heapTerm, tacitHeap);
        } else {
            // non-static field access
            lp.startTerm(3);
            lp.markStartSub(1);
            lp.printEmbeddedObserver(heapTerm, objectTerm);
            lp.markEndSub();
            lp.layouter.print(".");
            lp.markStartSub(2);
            if (isCanonicField(objectTerm, fieldTerm)) {
                /*
                 * Class name can be omitted if the field is canonic, i.e.
                 * correct field can be determined without explicit mentioning
                 * of corresponding class name.
                 *
                 * Example syntax: object.field
                 */
                lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
            } else {
                /*
                 * There is another field of the same name that would be selected
                 * if class name is omitted. In this case class name must be mentioned
                 * explicitly.
                 *
                 * Example syntax: object.(package.class::field)
                 */
                lp.layouter.print("(");
                lp.layouter.print(fieldTerm.toString().replace("::$", "::"));
                lp.layouter.print(")");
            }
            lp.markEndSub();
            printHeap(heapTerm, tacitHeap);
        }
    }

    /*
     * Print a term of the form: any::select(heap, object, field).
     */
    private void printAnySelect(final Term heapTerm, final Term objectTerm, final Term fieldTerm, Term tacitHeap) throws IOException {
        lp.startTerm(3);
        lp.markStartSub(1);
        lp.printEmbeddedObserver(heapTerm, objectTerm);
        lp.markEndSub();
        lp.layouter.print(".");
        lp.markStartSub(2);
        lp.printTerm(fieldTerm);
        lp.markEndSub();
        printHeap(heapTerm, tacitHeap);
    }

    /*
     * Print out a select on an array.
     */
    private void printArraySelect(Term heapTerm, Term objectTerm,
            Term fieldTerm, Term tacitHeap) throws IOException {

        lp.startTerm(3);
        lp.markStartSub(1);
        lp.printEmbeddedObserver(heapTerm, objectTerm);
        lp.markEndSub();

        lp.layouter.print("[");
        lp.markStartSub();
        lp.startTerm(2);
        lp.markStartSub();
        lp.printTerm(fieldTerm.sub(0));
        lp.markEndSub();
        lp.markEndSub();
        lp.layouter.print("]");

        printHeap(heapTerm, tacitHeap);
    }

    /*
     * This is used to check whether the <created>-field is targeted by a 
     * select-term. That means the select-term is similar to the following:
     * boolean::select( ... , ... , java.lang.Object::<created>)
     */
    private boolean isSelectOnCreated(Term fieldTerm, Sort selectSort) {
        return selectSort.equals(lp.services.getTypeConverter().getBooleanLDT().targetSort())
                && fieldTerm.toString().equals("java.lang.Object::<created>");
    }

    /*
     * Print a select-term, which has the following form: 
     * boolean::select( ... , ... , java.lang.Object::<created>)
     */
    private void printCreated(Term heapTerm, Term objectTerm, Term tacitHeap) throws IOException {
        lp.startTerm(3);
        lp.markStartSub(1);
        lp.printEmbeddedObserver(heapTerm, objectTerm);
        lp.markEndSub();
        lp.layouter.print(".");
        lp.markStartSub(2);
        lp.printConstant("<created>");
        lp.markEndSub();
        printHeap(heapTerm, tacitHeap);
    }

}
