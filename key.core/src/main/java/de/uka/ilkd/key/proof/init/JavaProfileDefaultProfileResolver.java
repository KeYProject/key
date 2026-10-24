/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.init;

import org.jspecify.annotations.NullMarked;

/**
 * A {@link DefaultProfileResolver} which returns {@link JavaProfile#getDefaultProfile()}.
 *
 * @author Martin Hentschel
 */
@NullMarked
public class JavaProfileDefaultProfileResolver implements DefaultProfileResolver {
    /**
     * {@inheritDoc}
     */
    @Override
    public String getProfileName() {
        return JavaProfile.PROFILE_ID;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Profile getDefaultProfile() {
        return JavaProfile.getDefaultInstance();
    }
}
