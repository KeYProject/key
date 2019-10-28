package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.RuleKey;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.LinkedHashMap;

import java.util.List;
import java.util.Map;
import java.util.prefs.Preferences;

public class ParsedKeyFile {
    private final Map<RuleKey, Taclet> taclets = new LinkedHashMap<>();
    public List<Choice> seqChoices;
    public List<Object> contracts;
    public List<Object> invariants;
    public Term problemTerm;
    private String chooseContract;
    private String proofObligation;
    private String profile;
    private String preferences;
    private String bootClassPath, javaSource;
    private List<String> classpath;


    public Map<RuleKey, Taclet> getTaclets() {
        return taclets;
    }

    public String getChooseContract() {
        return chooseContract;
    }


    public void setChooseContract(String chooseContract) {
        this.chooseContract = chooseContract;
    }

    public String getProofObligation() {
        return proofObligation;
    }

    public void setProofObligation(String proofObligation) {
        this.proofObligation = proofObligation;
    }

    public String getProfile() {
        return profile;
    }

    public void setProfile(String profile) {
        this.profile = profile;
    }

    public String getPreferences() {
        return preferences;
    }

    public void setPreferences(String preferences) {
        this.preferences = preferences;
    }

    public String getBootClassPath() {
        return bootClassPath;
    }

    public void setBootClasspath(String bootClassPath) {
        this.bootClassPath = bootClassPath;
    }

    public String getJavaSource() {
        return javaSource;
    }

    public void setJavaSource(String javaSource) {
        this.javaSource = javaSource;
    }

    public List<String> getClasspath() {
        return classpath;
    }

    public void setClasspath(List<String> classpath) {
        this.classpath = classpath;
    }

    @Override
    public String toString() {
        return "ParsedKeyFile{" +
                "taclets=" + taclets +
                ", seqChoices=" + seqChoices +
                ", contracts=" + contracts +
                ", invariants=" + invariants +
                ", problemTerm=" + problemTerm +
                ", chooseContract='" + chooseContract + '\'' +
                ", proofObligation='" + proofObligation + '\'' +
                ", profile=" + profile +
                ", preferences=" + preferences +
                ", bootClassPath='" + bootClassPath + '\'' +
                ", javaSource='" + javaSource + '\'' +
                ", classpath=" + classpath +
                '}';
    }
}
