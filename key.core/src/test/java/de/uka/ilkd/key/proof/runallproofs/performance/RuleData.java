/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof.runallproofs.performance;

public class RuleData {

    int numberInvocations = 1;
    long duration;

    public RuleData(long computeCostDuration) {
        this.duration = computeCostDuration;
    }

    public void addDuration(long duration) {
        numberInvocations++;
        this.duration += duration;
    }

}
