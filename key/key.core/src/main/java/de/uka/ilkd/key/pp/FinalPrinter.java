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
 * This class is used by LogicPrinter.java to print out final-terms, i.e. terms
 * of the following form: T::final(heap, object, field)
 *
 * Almost exact copy of SelectPrinter without the heap printing.
 *
 * @author Julian Wiesler <wiesleju@gmail.com>
 */
class FinalPrinter extends FieldPrinter {

    FinalPrinter(LogicPrinter lp) {
        super(lp);
    }

    /*
     * Print a term of the form: T::final(object, field).
     */
    public void printFinal(Term t) throws IOException {
        assert t.boundVars().isEmpty();
        assert t.arity() == 2;
        HeapLDT heapLDT = lp.getHeapLDT();

        if (lp.notationInfo.isPrettySyntax() && heapLDT != null) {
            final Term objectTerm = t.sub(0);
            final Term fieldTerm = t.sub(1);
            // Array selects are never final, no need to handle them
            if (t.sort().equals(Sort.ANY)) {
                /*
                 * This section deals with PP of frame conditions (and similar).
                 * Select-type is any.
                 */
                if (isFieldName(fieldTerm.op().name().toString(), objectTerm)
                        || isJavaFieldConstant(fieldTerm)) {
                    lp.printFunctionTerm(t);
                } else {
                    printAnySelect(objectTerm, fieldTerm);
                }
            } else if (isBuiltinObjectProperty(fieldTerm)) {
                // object properties denoted like o.<created>
                printBuiltinObjectProperty(t, objectTerm, fieldTerm);
            } else if (isStaticFieldConstant(objectTerm, fieldTerm)
                    && getFieldSort(fieldTerm).equals(t.sort())) {
                // static field access
                printStaticJavaFieldConstant(fieldTerm);
            } else if (isJavaFieldConstant(fieldTerm)
                    && getFieldSort(fieldTerm).equals(t.sort())) {
                // non-static field access
                printNonStaticJavaFieldConstant(objectTerm, fieldTerm);
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
    private void printStaticJavaFieldConstant(
            final Term fieldTerm
    ) throws IOException {
        lp.startTerm(2);
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
            lp.markStartSub(0);
            lp.printTerm(lp.services.getTermBuilder().NULL());
            lp.markEndSub();
        } else {
            lp.markStartSub(0);
            // "null" not printed, print className (which is not a subterm)
            lp.markEndSub();
            lp.printClassName(className);
        }

        lp.layouter.print(".");
        lp.markStartSub(1);
        lp.startTerm(0);
        lp.layouter.print(HeapLDT.getPrettyFieldName(fieldTerm.op()));
        lp.markEndSub();
    }

    /*
     * Print a non-static field constant.
     */
    private void printNonStaticJavaFieldConstant(
            final Term objectTerm,
            final Term fieldTerm
    ) throws IOException {
        lp.startTerm(2);
        lp.markStartSub(0);
        lp.printTerm(objectTerm);
        lp.markEndSub();
        lp.layouter.print(".");
        lp.markStartSub(1);
        lp.startTerm(0);
        lp.layouter.print(getPrettySyntaxForFieldConstant(objectTerm, fieldTerm));
        lp.printLabels(fieldTerm);
        lp.markEndSub();
    }

    /*
     * Print a term of the form: any::final(heap, object, field).
     */
    private void printAnySelect(
            final Term objectTerm,
            final Term fieldTerm
    ) throws IOException {
        lp.startTerm(2);
        lp.markStartSub(0);
        lp.printTerm(objectTerm);
        lp.markEndSub();
        lp.layouter.print(".");
        lp.markStartSub(1);
        lp.printTerm(fieldTerm);
        lp.markEndSub();
    }

    /*
     * Print a select-term of the following form:
     *      T::final( ... , ... , java.lang.Object::<...>)
     * For example:
     *      boolean::final(heap, object, java.lang.Object::<created>)
     */
    private void printBuiltinObjectProperty(
            Term t,
            Term objectTerm,
            Term fieldTerm
    ) throws IOException {
        JavaInfo javaInfo = lp.services.getJavaInfo();
        KeYJavaType selectKJT = javaInfo.getKeYJavaType(t.sort());
        KeYJavaType objectKJT = javaInfo.getKeYJavaType(objectTerm.sort());

        if (selectKJT != null && objectKJT != null) {
            assert fieldTerm.op().name().toString().contains("::<");
            String prettyFieldName = HeapLDT.getPrettyFieldName(fieldTerm.op());
            ProgramVariable pv = javaInfo.getCanonicalFieldProgramVariable(prettyFieldName, objectKJT);

            if (pv != null && pv.sort().equals(t.sort())) {
                lp.startTerm(2);
                lp.markStartSub(0);
                lp.printTerm(objectTerm);
                lp.markEndSub();
                lp.layouter.print(".");
                lp.markStartSub(1);
                lp.printConstant(fieldTerm, prettyFieldName);
                lp.markEndSub();
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