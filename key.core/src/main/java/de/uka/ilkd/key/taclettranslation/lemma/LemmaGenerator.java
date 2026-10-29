/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.taclettranslation.lemma;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.TacletTranslator;

/**
 * A Lemma Generator translates a taclet to its corresponding first order logic formula thats
 * validity implies the validity of the taclet.
 */
public interface LemmaGenerator extends TacletTranslator {
    TacletFormula translate(Taclet taclet, TermServices services);
}
