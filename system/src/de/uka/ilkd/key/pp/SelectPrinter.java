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
class SelectPrinter extends FieldPrinter {

    SelectPrinter(LogicPrinter lp) {
        super(lp);
    }

    /*
     * Print a term of the form: T::select(heap, object, field).
     */
    public void printSelect(Term t, Term tacitHeap) throws IOException {
        assert t.boundVars().isEmpty();
        assert t.arity() == 3;
        HeapLDT heapLDT = lp.getHeapLDT();

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
                if (isFieldName(fieldTerm.op().name().toString(), objectTerm)
                        || isJavaFieldConstant(fieldTerm)) {
                    lp.printFunctionTerm(t);
                } else {
                    printAnySelect(heapTerm, objectTerm, fieldTerm, tacitHeap);
                }
            } else if (fieldTerm.op() == heapLDT.getArr()) {
                // array access
                printArraySelect(heapTerm, objectTerm, fieldTerm, tacitHeap);
            } else if (isGenericFieldConstant(fieldTerm)) {
                // object properties denoted like o.<created>
                printGenericObjectProperty(t, heapTerm, objectTerm, fieldTerm, tacitHeap);
            } else if (isFieldConstant(fieldTerm) && getFieldSort(fieldTerm).equals(t.sort())) {
                if (isStaticFieldConstant(objectTerm, fieldTerm)) {
                    // static field access
                    printStaticJavaFieldConstant(fieldTerm, heapTerm, tacitHeap);
                } else if (isJavaFieldConstant(fieldTerm)) {
                    // non-static field access
                    printNonStaticJavaFieldConstant(heapTerm, objectTerm, fieldTerm, tacitHeap);
                } else {
                    lp.printFunctionTerm(t);
                }
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
        String lookup = fieldTerm.op().toString().replace("$", "");
        ProgramVariable progVar = lp.services.getJavaInfo().getAttribute(lookup);
        return progVar.sort();
    }

    /*
     * Print a static field constant.
     */
    private void printStaticJavaFieldConstant(final Term fieldTerm, final Term heapTerm, Term tacitHeap) throws IOException {
        lp.startTerm(3);
        /*
         * Is consideration for static arrays missing in this?
         * (Kai Wallisch 08/2014)
         */

        String className = HeapLDT.getClassName((Function) fieldTerm.op());

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
        lp.startTerm(0);
        lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
        lp.markEndSub();

        printHeap(heapTerm, tacitHeap);
    }

    /*
     * Print a non-static field constant.
     */
    private void printNonStaticJavaFieldConstant(final Term heapTerm, final Term objectTerm, final Term fieldTerm, Term tacitHeap) throws IOException {
        lp.startTerm(3);
        lp.markStartSub(1);
        lp.printEmbeddedObserver(heapTerm, objectTerm);
        lp.markEndSub();
        lp.layouter.print(".");
        lp.markStartSub(2);
        lp.startTerm(0);
        lp.layouter.print(getPrettySyntaxForFieldConstant(objectTerm, fieldTerm));
        lp.markEndSub();
        printHeap(heapTerm, tacitHeap);
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
        lp.markStartSub(2);

        /*
         * Used to be startTerm(2).
         * Changed it to startTerm(1) because array has only 1 argument.
         * (Kai Wallisch 09/2014)
         */
        lp.startTerm(1);
        lp.markStartSub();
        lp.printTerm(fieldTerm.sub(0));
        lp.markEndSub();
        lp.markEndSub();
        lp.layouter.print("]");

        printHeap(heapTerm, tacitHeap);
    }

    /*
     * Print a select-term of the following form: 
     *      T::select( ... , ... , java.lang.Object::<...>)
     * For example:
     *      boolean::select(heap, object, java.lang.Object::<created>)
     */
    private void printGenericObjectProperty(Term t, Term heapTerm, Term objectTerm, Term fieldTerm, Term tacitHeap) throws IOException {

        JavaInfo javaInfo = lp.services.getJavaInfo();
        KeYJavaType selectKJT = javaInfo.getKeYJavaType(t.sort());
        KeYJavaType objectKJT = javaInfo.getKeYJavaType(objectTerm.sort());

        if (selectKJT != null && objectKJT != null) {

            assert fieldTerm.op().name().toString().contains("::<");
            String prettyFieldName = HeapLDT.getPrettyFieldName(fieldTerm.op());
            ProgramVariable pv = javaInfo.getCanonicalFieldProgramVariable(prettyFieldName, objectKJT);

            if (pv != null && pv.sort().equals(t.sort())) {
                lp.startTerm(3);
                lp.markStartSub(1);
                lp.printEmbeddedObserver(heapTerm, objectTerm);
                lp.markEndSub();
                lp.layouter.print(".");
                lp.markStartSub(2);
                lp.printConstant(prettyFieldName);
                lp.markEndSub();
                printHeap(heapTerm, tacitHeap);
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
