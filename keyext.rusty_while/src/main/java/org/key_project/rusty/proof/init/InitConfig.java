/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.settings.ProofSettings;


public class InitConfig {
    /**
     * the services class allowing to access information about the underlying program model
     */
    private final Services services;

    private ProofSettings settings;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public InitConfig(Services services) {
        this.services = services;
    }

    public void setSettings(ProofSettings newSettings) {
        this.settings = newSettings;
    }

    public ProofSettings getSettings() {
        return settings;
    }

    public Services getServices() {
        return services;
    }

    /**
     * returns the namespaces of this initial configuration
     */
    public NamespaceSet namespaces() {
        return services.getNamespaces();
    }
}
