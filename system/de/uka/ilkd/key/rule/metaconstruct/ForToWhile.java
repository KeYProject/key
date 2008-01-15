package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.ListOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SLListOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * converts a for-loop to a while loop. Invariant and other rules cannot be
 * performed on for but only on while loops.
 * 
 * It makes uses of the {@link ForToWhileTransformation} to create a transformed
 * loop body which is then put into the corresponding context.
 * 
 * <h2>Example</h2>
 * 
 * <pre>
 * for (int i = 0; i &lt; 100; i++) {
 *     if (i == 2)
 *         continue;
 *     if (i == 3)
 *         break;
 * }
 * </pre>
 * 
 * is translated to
 * 
 * <pre>
 * _label1: {
 *     int i = 0;
 *     while (i &lt; 100) {
 *         _label0: {
 *             if (i == 2)
 *                 break _label0;
 *             if (i == 3)
 *                 break _label1;
 *         }
 *         i++;
 *     }
 * }
 * </pre>
 * 
 * @see ForToWhileTransformation
 * @author MU
 */

public class ForToWhile extends ProgramMetaConstruct implements
        MetaConstructWithSV {

    /**
     * the outer label that is used to leave the while loop ('l1')
     */
    private final SchemaVariable outerLabel;

    /**
     * the inner label ('l2')
     */
    private final SchemaVariable innerLabel;

    /**
     * creates an loop to while - ProgramMetaConstruct
     * 
     * @param loop
     *            the LoopStatement contained by the meta construct
     * @param innerLabel
     *            the label used to handle continue
     * @param outerLabel
     *            the label used to handle break (only needed for
     *            do-while-loops)
     */
    public ForToWhile(SchemaVariable innerLabel, SchemaVariable outerLabel,
            Statement loop) {
        super("#for-to-while", loop);
        this.innerLabel = innerLabel;
        this.outerLabel = outerLabel;

    }

    /**
     * performs the necessary transformation using a LoopToWhileTransformation
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
            Services services, SVInstantiations svInst) {

        WhileLoopTransformation w = new ForToWhileTransformation(pe,
                (ProgramElementName) svInst.getInstantiation(outerLabel),
                (ProgramElementName) svInst.getInstantiation(innerLabel),
                services);

        w.start();
        return w.result();
    }

    /**
     * return a list of the SV that are relevant to this UnwindLoop
     * 
     * @param originalLoop
     *            the loop to work upon - ignored
     * @param svInst
     *            the instantiations so far - ignored
     * @return a list of 0 to 2 schema variables (outer/inner label)
     */
    public ListOfSchemaVariable neededInstantiations(SVInstantiations svInst) {
        ListOfSchemaVariable ret = SLListOfSchemaVariable.EMPTY_LIST;

        if (innerLabel != null)
            ret = ret.prepend(innerLabel);

        if (outerLabel != null)
            ret = ret.prepend(outerLabel);

        return ret;
    }
}
