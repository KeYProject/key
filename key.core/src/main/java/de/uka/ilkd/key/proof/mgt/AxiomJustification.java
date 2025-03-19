/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.mgt;


public class AxiomJustification implements RuleJustification {

    public static final AxiomJustification INSTANCE = new AxiomJustification();

    private AxiomJustification() {
    }

    public String toString() {
        return "axiom justification";
    }

    public boolean isAxiomJustification() {
        return true;
    }
}
