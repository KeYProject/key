package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Common superclass of {@link StorePrinter} and {@link SelectPrinter}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
class FieldPrinter {

    protected final LogicPrinter lp;

    FieldPrinter(LogicPrinter lp) {
        this.lp = lp;
    }

    /**
     * Determine the syntax in which a field constant is printed when associated
     * with the object represented by {@code objectTerm} Default is the name of
     * the field. In case the field is hidden by another field, the name of the
     * field is preceeded by the corresponding class name.
     *
     * Example default: object.field Example hidden field:
     * object.(package.class::field)
     *
     * Remark: This method is declared static because it is also used in method
     * {@link StorePrinter#printStoreOnFieldConstant(de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.logic.Term, boolean) }
     */
    protected String getPrettySyntaxForFieldConstant(Term objectTerm,
            Term fieldTerm) {

        JavaInfo javaInfo = lp.services.getJavaInfo();

        if (isCanonicField(objectTerm, fieldTerm, javaInfo)) {
            /*
             * Class name can be omitted if the field is canonic, i.e.
             * correct field can be determined without explicit mentioning
             * of corresponding class name.
             *
             * Example syntax: object.field
             */
            return HeapLDT.getPrettyFieldName(fieldTerm.op());
        } else {
            /*
             * There is another field of the same name that would be selected
             * if class name is omitted. In this case class name must be mentioned
             * explicitly.
             *
             * Example syntax: object.(package.class::field)
             */
            return "(" + fieldTerm.toString().replace("::$", "::") + ")";
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
    private boolean isCanonicField(Term objectTerm,
            Term fieldTerm,
            JavaInfo javaInfo) {
        Sort sort = objectTerm.sort();
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
     * Determine whether a term is a constant function symbol of type field.
     */
    protected static boolean isFieldConstant(Term fieldTerm, HeapLDT heapLDT) {
        return fieldTerm.op() instanceof Function
                && ((Function) fieldTerm.op()).isUnique()
                && fieldTerm.sort() == heapLDT.getFieldSort()
                && fieldTerm.arity() == 0
                && fieldTerm.boundVars().isEmpty();
    }

    protected boolean isFieldConstant(Term fieldTerm) {
        return isFieldConstant(fieldTerm, lp.getHeapLDT());
    }

    /**
     * Find out whether a {@link Term} represents a field symbol, declared in a
     * Java class.
     *
     * @return Returns true iff the given parameter represents a field constant.
     * @param fieldTerm The target field.
     */
    protected static boolean isJavaFieldConstant(Term fieldTerm, HeapLDT heapLDT) {
        return fieldTerm.op().name().toString().contains("::$")
                && isFieldConstant(fieldTerm, heapLDT);
    }

    protected boolean isJavaFieldConstant(Term fieldTerm) {
        return isJavaFieldConstant(fieldTerm, lp.getHeapLDT());
    }

    /*
     * Determine whether the field constant is a generic object property.
     * Those are surrounded by angle brackets, e.g. o.<created>
     */
    protected boolean isGenericFieldConstant(Term fieldTerm) {
        return fieldTerm.op().name().toString().contains("::<")
                && isFieldConstant(fieldTerm, lp.getHeapLDT());
    }

    /*
     * Determine whether a field constant is static.
     * Field constants are considered static if reference object
     * is null.
     */
    protected boolean isStaticFieldConstant(Term objectTerm, Term fieldTerm) {
        return objectTerm.equals(lp.services.getTermBuilder().NULL())
                && isFieldConstant(fieldTerm, lp.getHeapLDT());
    }

}
