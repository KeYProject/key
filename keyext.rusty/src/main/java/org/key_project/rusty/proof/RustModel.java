/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.io.File;
import java.text.DateFormat;
import java.util.Date;

import org.key_project.rusty.proof.init.Includes;

public final class RustModel {
    /**
     * Directory of Rust source files. May be null if the proof doesn't refer to any Rust code.
     */
    private final String modelDir;
    private final String modelTag;
    private final String descr;
    private final String includedFiles;
    private final File initialFile;

    public static final RustModel NO_MODEL = new RustModel();

    public static RustModel create(String rustPath, Includes includes, File initialFile) {
        RustModel result = null;
        if (rustPath == null) {
            result = NO_MODEL;
        } else {
            result = new RustModel(rustPath, includes, initialFile);
        }
        return result;
    }

    private RustModel() {
        this.modelDir = null;
        this.modelTag = null;
        this.descr = "no model";
        this.includedFiles = null;
        this.initialFile = null;
    }

    private RustModel(String rustPath, Includes includes, File initialFile) {
        File file = new File(rustPath);
        modelDir = file.getAbsolutePath();
        Date date = new Date();
        modelTag = "KeY_" + date.getTime();
        descr = "model " + file.getName() + "@"
            + DateFormat.getTimeInstance(DateFormat.MEDIUM).format(date);
        var sb = new StringBuilder();
        if (includes != null) {
            var includeList = includes.getFiles();
            if (!includeList.isEmpty()) {
                for (File f : includeList) {
                    sb.append("\"").append(f.getAbsolutePath()).append("\", ");
                }
                sb.setLength(sb.length() - 2);
            }
        }
        includedFiles = sb.toString();
        this.initialFile = initialFile;
    }

    public String getModelDir() {
        return modelDir;
    }

    public String getModelTag() {
        return modelTag;
    }

    public File getInitialFile() {
        return initialFile;
    }

    public String getIncludedFiles() {
        return includedFiles;
    }

    public boolean isEmpty() {
        return this == NO_MODEL;
    }

    public String description() {
        return descr;
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        final var other = (RustModel) o;
        if (getModelTag() == null) {
            return other.getModelTag() == null;
        }
        return getModelTag().equals(other.getModelTag());
    }
}
