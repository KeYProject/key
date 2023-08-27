/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.util.LinkedList;
import java.util.List;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

/**
 * This POJO represents the static information of a KeY problem. It can be extracted directly via
 * {@link FindProblemInformation}, without any previous interpretation of the AST.
 * <p>
 * This class contains rather the <i>raw</i> information, e.g. classpaths are not completed with
 * current working dir. Rather the values are provided as in the {@link KeyAst.File}. Further work
 * may require, like in {@link KeYFile#readJavaPath()}.
 * </p>
 *
 * @author weigl
 * @see FindProblemInformation
 */
public class ProblemInformation {
    /**
     * A list of class paths entries.
     */
    private final @Nonnull List<String> classpath;

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

    @Nullable
    public String getChooseContract() {
        return chooseContract;
    }

    public void setChooseContract(@Nullable String chooseContract) {
        this.chooseContract = chooseContract;
    }

    @Nullable
    public String getProofObligation() {
        return proofObligation;
    }

    public void setProofObligation(@Nullable String proofObligation) {
        this.proofObligation = proofObligation;
    }

    @Nullable
    public String getProfile() {
        return profile;
    }

    public void setProfile(@Nullable String profile) {
        this.profile = profile;
    }

    @Nullable
    public String getPreferences() {
        return preferences;
    }

    public void setPreferences(@Nullable String preferences) {
        this.preferences = preferences;
    }

    @Nullable
    public String getBootClassPath() {
        return bootClassPath;
    }

    public void setBootClassPath(@Nullable String bootClassPath) {
        this.bootClassPath = bootClassPath;
    }

    @Nullable
    public String getJavaSource() {
        return javaSource;
    }

    public void setJavaSource(@Nullable String javaSource) {
        this.javaSource = javaSource;
    }

    @Nonnull
    public List<String> getClasspath() {
        return classpath;
    }

    public boolean isHasProblemTerm() {
        return hasProblemTerm;
    }

    public void setHasProblemTerm(boolean hasProblemTerm) {
        this.hasProblemTerm = hasProblemTerm;
    }
}
