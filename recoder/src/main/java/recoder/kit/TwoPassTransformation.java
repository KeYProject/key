/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import recoder.CrossReferenceServiceConfiguration;

/**
 * A two-pass transformation is a nice special case of a transformation, where all
 * subtransformations do not conflict, or where conflicts between them can be resolved locally. This
 * allows to split the protocol into a pure analysis and a pure syntactic transformation phase, such
 * that model updates during the execution are not necessary. Transformations that only use two-pass
 * transformations are also two-pass transformations.
 * <p>
 * The transformation execution phase of a one-pass transformation is now split into:
 * <UL>
 * <LI>Analysis (analyze): Collect all semantic information via queries to the info services and
 * store them for the syntactic changes but do not change anything yet. Estimate the effects of the
 * transformation, set and return the problem report. Note that analyses are possible for visible
 * parts of the model only.
 * <LI>Transformation (transform): Use the analysis results to perform syntactic changes. Do not
 * perform any query that might lead to a model update - only traversals in the syntax trees are
 * allowed. Visible transformations must report all changes they have done to the change history and
 * must mark their beginning before the first change. Changes are already reported by the
 * convenience tree manipulators attach(Role)/detach/replace. The beginning is already reported by
 * the default implementation of {@link #transform()}, available via a
 * <CODE>super.transform()</CODE> call.
 * </UL>
 */
public abstract class TwoPassTransformation extends Transformation {

    /**
     * Creates a new transformation leaving open the given service configuration. This is useful for
     * bean-like transformation management.
     */
    protected TwoPassTransformation() {
        super();
    }

    /**
     * Creates a new transformation using the given service configuration.
     *
     * @param sc the service configuration to use.
     */
    public TwoPassTransformation(CrossReferenceServiceConfiguration sc) {
        super(sc);
    }

    /**
     * Prepares all necessary information for the syntactic transformation and checks the
     * transformation requirements. This method may call any queries but may not change the model
     * directly (the model might be augmented by automatic reload, however). This default
     * implementation sets and returns {@link #NO_PROBLEM}.
     *
     * @return a problem report, an instance of {@link recoder.kit.NoProblem}if all requirements
     *         have been met.
     */
    public ProblemReport analyze() {
        setProblemReport(NO_PROBLEM);
        return NO_PROBLEM;
    }

    /**
     * Performs the syntactic transformation. This method may not call any query that may lead to a
     * model update. If this transformation is visible, change reports are send to the change
     * history. The default implementation will check if the problem report has been initialized,
     * and report the begin of the transformation to the change history if this transformation is
     * visible. Redefined methods should call this method via <CODE>
     * super.transform()</CODE> as the first action.
     *
     * @throws IllegalStateException if the analysis did not initialize the report.
     * @see #analyze()
     * @see #isVisible()
     * @see recoder.service.ChangeHistory#begin(Transformation)
     */
    public void transform() {
        if (getProblemReport() == null) {
            throw new IllegalStateException("No analyze");
        }
        if (isVisible()) {
            getChangeHistory().begin(this);
        }
    }

    /**
     * Convenience template method that calls {@link #analyze()}and {@link #transform()}if the
     * result was {@link recoder.kit.NoProblem}and not {@link recoder.kit.Identity}.
     */
    public ProblemReport execute() {
        ProblemReport report = analyze();
        if ((report instanceof NoProblem) && !(report instanceof Identity)) {
            transform();
        }
        return report;
    }

}
