/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.init;

/**
 * A {@link DefaultProfileResolver} which returns {@link JavaProfile#defaultInstancePermissions}.
 *
 * @author Martin Hentschel
 */
public class JavaProfileWithPermissionsDefaultProfileResolver implements DefaultProfileResolver {
    /**
     * {@inheritDoc}
     */
    @Override
    public String getProfileName() {
        return JavaProfile.NAME_WITH_PERMISSIONS;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Profile getDefaultProfile() {
        return JavaProfile.getDefaultInstance(true);
    }
}
