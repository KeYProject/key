/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.profile;

import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.Profile;

/**
 * A {@link DefaultProfileResolver} which returns
 * {@link SymbolicExecutionJavaProfile#getDefaultInstance()}.
 *
 * @author Martin Hentschel
 */
public class SymbolicExecutionJavaProfileDefaultProfileResolver implements DefaultProfileResolver {
    /**
     * {@inheritDoc}
     */
    @Override
    public String getProfileName() {
        return SymbolicExecutionJavaProfile.NAME;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Profile getDefaultProfile() {
        return SymbolicExecutionJavaProfile.getDefaultInstance();
    }
}
