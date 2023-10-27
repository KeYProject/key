/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.java.declaration.VariableSpecification;
import recoder.java.reference.VariableReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;

/**
 * Transformation that renames a variable by renaming all known references to that variable. The new
 * name should not be used for another variable.
 * <p>
 * <B>Implementation warning: </B> does not (yet) check vadility of new name in the context; does
 * not check if there are byte code types that cannot be changed
 *
 * @author AL
 */
public class RenameVariable extends TwoPassTransformation {

    private final VariableSpecification vs;

    private final String newName;

    private List<VariableReference> refs;

    /**
     * Creates a new transformation object that renames a variable and all references to it. The new
     * name should not conflict with another variable.
     *
     * @param sc the service configuration to use.
     * @param vs the variable to be renamed; may not be <CODE>null</CODE>.
     * @param newName the new name for the element; may not be <CODE>null</CODE> and must denote a
     *        valid identifier name.
     */
    public RenameVariable(CrossReferenceServiceConfiguration sc, VariableSpecification vs,
            String newName) {
        super(sc);
        if (vs == null) {
            throw new IllegalArgumentException("Missing variable");
        }
        if (newName == null) {
            throw new IllegalArgumentException("Missing name");
        }
        this.vs = vs;
        this.newName = newName;
    }

    /**
     * Collects all references to the variable.
     *
     * @return the problem report.
     */
    public ProblemReport analyze() {
        refs = new ArrayList<>();
        if (newName.equals(vs.getName())) {
            return setProblemReport(IDENTITY);
        }
        refs.addAll(getCrossReferenceSourceInfo().getReferences(vs));
        return setProblemReport(EQUIVALENCE);
    }

    /**
     * Locally renames all variable references collected in the analyzation phase.
     *
     * @throws IllegalStateException if the analyzation has not been called.
     * @see #analyze()
     */
    public void transform() {
        super.transform();
        ProgramFactory pf = getProgramFactory();
        replace(vs.getIdentifier(), pf.createIdentifier(newName));
        for (int i = refs.size() - 1; i >= 0; i -= 1) {
            replace(refs.get(i).getIdentifier(), pf.createIdentifier(newName));
        }
    }
}
