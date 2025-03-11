/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

/**
 * A {@link DefaultProfileResolver} which returns {@link JavaProfile#getDefaultProfile()}.
 *
 * @author Martin Hentschel
 */
public class JavaProfileDefaultProfileResolver implements DefaultProfileResolver {
    /**
     * {@inheritDoc}
     */
    @Override
    public String getProfileName() {
        return JavaProfile.NAME;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Profile getDefaultProfile() {
        return JavaProfile.getDefaultInstance();
    }
}
