/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.Profile;

/**
 * @author Alexander Weigl
 * @version 1 (8/3/25)
 */
public class WdProfileResolver implements DefaultProfileResolver {
    @Override
    public String getProfileName() {
        return "java-wd";
    }

    @Override
    public Profile getDefaultProfile() {
        return WdProfile.INSTANCE;
    }
}
