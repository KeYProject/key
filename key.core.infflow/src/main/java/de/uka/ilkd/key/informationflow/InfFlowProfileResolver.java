/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow;

import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.Profile;

public class InfFlowProfileResolver implements DefaultProfileResolver {
    @Override
    public String getProfileName() {
        return "java-infflow";
    }

    @Override
    public Profile getDefaultProfile() {
        return new JavaInfFlowProfile();
    }
}
