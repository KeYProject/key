/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.profile;

import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.Profile;

/**
 * Registers the {@link JvmProfile} with the {@link DefaultProfileResolver} service loader, so it
 * can be selected by name ("java-jvm") exactly like the well-definedness profile ("java-wd").
 * <p>
 * Wired via {@code META-INF/services/de.uka.ilkd.key.proof.init.DefaultProfileResolver}. Resolvers
 * are treated as singletons and must be stateless.
 */
public class JvmProfileResolver implements DefaultProfileResolver {
    @Override
    public String getProfileName() {
        return JvmProfile.PROFILE_ID;
    }

    @Override
    public Profile getDefaultProfile() {
        return JvmProfile.INSTANCE;
    }
}
