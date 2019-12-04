package de.uka.ilkd.key.nparser;

import java.util.LinkedList;
import java.util.List;

public class ProblemInformation {
    private String chooseContract;
    private String proofObligation;
    private String profile;
    private String preferences;
    private String bootClassPath, javaSource;
    private List<String> classpath = new LinkedList<>();

    public ProblemInformation() {
    }

    public ProblemInformation(String chooseContract, String proofObligation, String profile, String preferences, String bootClassPath, String javaSource, List<String> classpath) {
        this.chooseContract = chooseContract;
        this.proofObligation = proofObligation;
        this.profile = profile;
        this.preferences = preferences;
        this.bootClassPath = bootClassPath;
        this.javaSource = javaSource;
        this.classpath = classpath;
    }

    public String getChooseContract() {
        return chooseContract;
    }

    void setChooseContract(String chooseContract) {
        this.chooseContract = chooseContract;
    }

    public String getProofObligation() {
        return proofObligation;
    }

    void setProofObligation(String proofObligation) {
        this.proofObligation = proofObligation;
    }

    public String getProfile() {
        return profile;
    }

    void setProfile(String profile) {
        this.profile = profile;
    }

    public String getPreferences() {
        return preferences;
    }

    void setPreferences(String preferences) {
        this.preferences = preferences;
    }

    public String getBootClassPath() {
        return bootClassPath;
    }

    void setBootClassPath(String bootClassPath) {
        this.bootClassPath = bootClassPath;
    }

    public String getJavaSource() {
        return javaSource;
    }

    void setJavaSource(String javaSource) {
        this.javaSource = javaSource;
    }

    public List<String> getClasspath() {
        return classpath;
    }

    void setClasspath(List<String> classpath) {
        this.classpath = classpath;
    }
}
