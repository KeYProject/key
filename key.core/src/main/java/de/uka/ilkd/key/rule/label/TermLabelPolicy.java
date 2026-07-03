/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelContext;
import de.uka.ilkd.key.logic.label.TermLabelManager;


/**
 * <p>
 * A {@link TermLabelPolicy} is used by
 * {@link TermLabelManager#instantiateLabels}
 * to decide for each {@link TermLabel} of an old {@link JTerm} if it should be re-added to the new
 * {@link JTerm} or not. Policies are registered per label {@link org.key_project.logic.Name} and
 * are only asked for labels of that name.
 * </p>
 * <p>
 * <b>Execution order (part of the contract):</b> within one term creation, policies run
 * <em>before</em> all {@link TermLabelUpdate}s — first the application-term policies, then the
 * modality-term policies. The label set produced by the policies is what the updates subsequently
 * see and may transform. Do not design a label whose update must run before a policy.
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
public interface TermLabelPolicy {
    /**
     * Decides to keep (add to term which will be created) or to drop (do not add label to new term)
     * the given {@link TermLabel} provided by the source {@link JTerm}.
     *
     * @param context the {@link TermLabelContext} of the current rule application
     * @param sourceTerm the {@link JTerm} whose labels are under consideration: the application
     *        term for application-term policies, the modality term for modality-term policies
     * @param newTerm the template for the new {@link JTerm} to create
     * @param label The {@link TermLabel} to decide if it should be kept or dropped.
     * @return The {@link TermLabel} to keep which might be a different one (e.g. with changed
     *         parameters) or {@code null} if the {@link TermLabel} should be dropped.
     */
    TermLabel keepLabel(TermLabelContext context, JTerm sourceTerm, JTerm newTerm,
            TermLabel label);
}
