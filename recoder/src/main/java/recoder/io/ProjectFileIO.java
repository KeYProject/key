/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.io;

import java.io.IOException;

import recoder.ServiceConfiguration;

/**
 * Facility to import and export project settings in various project files.
 *
 * @since 0.63
 */
public abstract class ProjectFileIO {

    private final ServiceConfiguration config;

    public ProjectFileIO(ServiceConfiguration system) {
        config = system;
    }

    protected ServiceConfiguration getServiceConfiguration() {
        return config;
    }

    protected SourceFileRepository getSourceFileRepository() {
        return config.getSourceFileRepository();
    }

    protected ProjectSettings getProjectSettings() {
        return config.getProjectSettings();
    }

    /**
     * Loads properties from the project file and returns the file names of the compilation units
     * stored in the project file. It is left to subclasses to locate the project file.
     *
     * @return the filenames of the known compilation units.
     */
    public abstract String[] load() throws IOException;

    /**
     * Saves the project properties to the project file and adds all known compilation units. This
     * method does not write back the compilation units themselves. It is left to subclasses to
     * locate the project file.
     */
    public abstract void save() throws IOException;
}
