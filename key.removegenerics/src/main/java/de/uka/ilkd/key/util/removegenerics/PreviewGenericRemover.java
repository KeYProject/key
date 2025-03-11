/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.removegenerics;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.util.removegenerics.monitor.GenericRemoverMonitor;

import recoder.io.DataFileLocation;
import recoder.io.DataLocation;
import recoder.java.CompilationUnit;

public class PreviewGenericRemover extends AbstractGenericRemover {
    private final Map<File, String> resultMap = new HashMap<>();

    public PreviewGenericRemover(GenericRemoverMonitor monitor) {
        super(monitor);
    }

    @Override
    protected void saveModifiedCompilationUnit(CompilationUnit cu, String filename)
            throws IOException {
        DataLocation location = cu.getDataLocation();
        assert location instanceof DataFileLocation;
        DataFileLocation fileLocation = (DataFileLocation) location;
        resultMap.put(fileLocation.getFile(), cu.toSource());
    }

    public Map<File, String> getResultMap() {
        return resultMap;
    }
}
