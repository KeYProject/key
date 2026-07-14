/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.util.parsing.Location;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * This POJO represents the static information of a KeY problem. It can be extracted directly via
 * {@link de.uka.ilkd.key.nparser.builder.FindProblemInformation}, without any previous
 * interpretation of the AST.
 * <p>
 * This class contains rather the <i>raw</i> information, e.g. classpaths are not completed with
 * current working dir. Rather the values are provided as in the {@link KeyAst.File}. Further work
 * may require, like in {@link de.uka.ilkd.key.proof.io.KeYFile#readJavaPath()}.
 * </p>
 *
 * @author weigl
 * @see de.uka.ilkd.key.nparser.builder.FindProblemInformation
 */
public class ProblemInformation {
    /**
     * A list of class paths entries.
     */
    private final @NonNull List<String> classpath;

    /**
     * The source location (file + position) at which each {@code \classpath}/{@code \bootclasspath}
     * value was declared, keyed by the raw path string. Used to point error messages (e.g. "the
     * directory does not exist") at the declaration in the {@code .key} file.
     */
    private final @NonNull Map<String, Location> pathLocations = new HashMap<>();

    /**
     * Value of a "\chooseContract". If "\chooseContract" are mentioned in the file, but without a
     * value, this field is non-null and empty.
     */
    private @Nullable String chooseContract;

    /**
     * Value of a "\proofObligation". If "\proofObligation" are mentioned in the file, but without a
     * value, this field is non-null and empty.
     */
    private @Nullable String proofObligation;


    /**
     * Value of a "\profile".
     */
    private @Nullable String profile;

    /**
     * Value of the "\preferences".
     */
    private @Nullable String preferences;

    /**
     * Value of the "\bootClasspath".
     */
    private @Nullable String bootClassPath;

    /**
     * Value of the "\javaSource".
     */
    private @Nullable String javaSource;

    /**
     *
     */
    private boolean hasProblemTerm;

    public ProblemInformation() {
        classpath = new LinkedList<>();
    }

    public @Nullable String getChooseContract() {
        return chooseContract;
    }

    public void setChooseContract(@Nullable String chooseContract) {
        this.chooseContract = chooseContract;
    }

    public @Nullable String getProofObligation() {
        return proofObligation;
    }

    public void setProofObligation(@Nullable String proofObligation) {
        this.proofObligation = proofObligation;
    }

    public @Nullable String getProfile() {
        return profile;
    }

    public void setProfile(@Nullable String profile) {
        this.profile = profile;
    }

    public @Nullable String getPreferences() {
        return preferences;
    }

    public void setPreferences(@Nullable String preferences) {
        this.preferences = preferences;
    }

    /**
     * Records the source location at which the given classpath/bootclasspath value was declared.
     *
     * @param path the raw path string
     * @param location its location in the {@code .key} file
     */
    public void putPathLocation(@NonNull String path, @NonNull Location location) {
        pathLocations.put(path, location);
    }

    /**
     * @param path a raw classpath/bootclasspath string
     * @return the location at which it was declared, or {@code null} if unknown
     */
    public @Nullable Location getPathLocation(@Nullable String path) {
        return path == null ? null : pathLocations.get(path);
    }

    public @Nullable String getBootClassPath() {
        return bootClassPath;
    }

    public void setBootClassPath(@Nullable String bootClassPath) {
        this.bootClassPath = bootClassPath;
    }

    public @Nullable String getJavaSource() {
        return javaSource;
    }

    public void setJavaSource(@Nullable String javaSource) {
        this.javaSource = javaSource;
    }

    public @NonNull List<String> getClasspath() {
        return classpath;
    }

    public boolean isHasProblemTerm() {
        return hasProblemTerm;
    }

    public void setHasProblemTerm(boolean hasProblemTerm) {
        this.hasProblemTerm = hasProblemTerm;
    }
}
