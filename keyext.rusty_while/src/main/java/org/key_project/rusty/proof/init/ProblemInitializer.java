/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;

import org.key_project.rusty.Services;


public final class ProblemInitializer {
    private static InitConfig baseConfig;
    private final Services services;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public ProblemInitializer(Services services) {
        this.services = services;
    }

    public ProblemInitializer(Profile profile) {
        if (profile == null) {
            throw new IllegalArgumentException("Given profile is null");
        }

        this.services = new Services();
    }


}
