/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import java.util.Set;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelContext;
import de.uka.ilkd.key.logic.label.TermLabelManager;


/**
 * <p>
 * A {@link TermLabelUpdate} is used by {@link TermLabelManager#instantiateLabels} to add or
 * remove maintained {@link TermLabel}s which will be added to the new {@link JTerm}.
 * </p>
 * <p>
 * <b>Execution order (part of the contract):</b> updates run <em>after</em> all
 * {@link TermLabelPolicy} instances; the label set passed to {@code updateLabels} already
 * contains the taclet-provided labels and the labels kept by the policies. Rule-specific updates
 * (see {@link #getSupportedRuleNames()}) run before rule-independent ones.
 * </p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained during proof
 * construction read the documentation of interface {@link TermLabel}.
 * </p>
 *
 * @author Martin Hentschel
 * @see TermLabel
 * @see TermLabelManager
 */
public interface TermLabelUpdate extends RuleSpecificTask {
    /**
     * This method can freely add, remove or sort the given {@link TermLabel}s which will be added
     * to the new {@link JTerm}.
     *
     * @param context the {@link TermLabelContext} of the current rule application
     * @param newTerm the template for the new {@link JTerm} to create
     * @param labels The {@link Set} of {@link TermLabel}s to modify.
     */
    void updateLabels(TermLabelContext context, JTerm newTerm, Set<TermLabel> labels);
}
