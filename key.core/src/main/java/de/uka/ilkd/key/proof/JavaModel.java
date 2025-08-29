/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.nio.file.Path;
import java.text.DateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.proof.init.Includes;

import org.key_project.util.java.IOUtil;

import org.jspecify.annotations.Nullable;

public final class JavaModel {

    /**
     * Directory of Java source files. May be null if the proof doesn't refer to any Java code.
     */
    private final @Nullable Path modelDir;
    private final @Nullable String modelTag;
    private final String descr;
    private final List<Path> classPath;
    private final Path bootClassPath;
    private final List<Path> includedFiles;
    private final Path initialFile;

    public static final JavaModel NO_MODEL = new JavaModel();


    /**
     *
     */
    public static JavaModel createJavaModel(
            Path javaPath,
            List<Path> classPath,
            Path bootClassPath, Includes includes, Path initialFile) {
        JavaModel result;
        if (javaPath == null) {
            result = NO_MODEL;
        } else {
            result = new JavaModel(javaPath, classPath, bootClassPath, includes, initialFile);
        }
        return result;
    }


    private JavaModel() {
        modelDir = null;
        modelTag = null;
        descr = "no model";
        classPath = null;
        bootClassPath = null;
        includedFiles = null;
        initialFile = null;
    }

    private JavaModel(Path modelDir,
            @Nullable List<Path> classPath,
            @Nullable Path bootClassPath,
            Includes includes, Path initialFile) {
        this.modelDir = modelDir;
        this.modelTag = "KeY_" + (new Date()).getTime();
        this.descr = "model " + modelDir.getFileName() + "@"
            + DateFormat.getTimeInstance(DateFormat.MEDIUM).format(new Date());

        if (classPath != null) {
            this.classPath = new ArrayList<>(classPath);
        } else {
            this.classPath = new ArrayList<>();
        }
        this.bootClassPath = bootClassPath == null ? null : bootClassPath.toAbsolutePath();
        this.includedFiles = new ArrayList<>(includes.getFiles());
        this.initialFile = initialFile;
    }

    public @Nullable Path getModelDir() {
        return modelDir;
    }

    public String getModelTag() {
        return modelTag;
    }

    public List<Path> getClassPath() {
        return classPath;
    }

    public Path getBootClassPath() {
        return bootClassPath;
    }

    public List<Path> getIncludedFiles() {
        return includedFiles;
    }

    public Path getInitialFile() {
        return initialFile;
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
        final JavaModel other = (JavaModel) o;
        if (getModelTag() == null) {
            return other.getModelTag() == null;
        } else {
            return getModelTag().equals(other.getModelTag());
        }
    }


    @Override
    public int hashCode() {
        if (getModelTag() == null) {
            return 42;
        } else {
            return getModelTag().hashCode();
        }
    }


    @Override
    public String toString() {
        return "---Program model---\nModel dir: " + modelDir + "\nModel tag: " + modelTag
            + "\nDescription: " + descr;
    }

    /// Transform the current state into a string with valid declarations inside a KeY file.
    /// In particular, it uses `\bootclasspath`, `\classpath`, `\javaSource` and `\includes`
    /// directive
    /// if necessary.
    public String asKeyString() {
        return (bootClassPath != null
                ? "\n\\bootclasspath \"%s\";".formatted(IOUtil.safePath(bootClassPath))
                : "") +
                (classPath != null && !classPath.isEmpty() ? "\n\\classpath %s;".formatted(
                    classPath.stream().map(IOUtil::safePath)
                            .map("\"%s\""::formatted)
                            .collect(Collectors.joining(", ")))
                        : "")
                +
                (modelDir != null ? "\n\\javaSource \"%s\";".formatted(IOUtil.safePath(modelDir))
                        : "")
                +
                (includedFiles != null && !includedFiles.isEmpty() ? "\n\\include %s;".formatted(
                    includedFiles.stream().map(IOUtil::safePath)
                            .map("\"%s\""::formatted)
                            .collect(Collectors.joining(", ")))
                        : "");
    }
}
