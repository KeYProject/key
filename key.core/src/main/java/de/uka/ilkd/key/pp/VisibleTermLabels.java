/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.TermLabel;

/**
 * This abstract class is used by SequentViewLogicPrinter to determine the set of printed
 * TermLabels.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public interface VisibleTermLabels {
    boolean contains(TermLabel label);

    boolean contains(Name name);
}
