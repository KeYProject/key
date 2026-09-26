/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.mgt;

/**
 * {@link RuleJustification} for taclets, that can be proven from other taclets.
 */
public class LemmaJustification implements RuleJustification {

    public static final LemmaJustification INSTANCE = new LemmaJustification();

    private LemmaJustification() {
    }

    @Override
    public boolean isAxiomJustification() {
        return false;
    }
}
