package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.RuleKey;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.LinkedHashMap;

import java.util.List;
import java.util.Map;

public class ParsedKeyFile {
    private final Map<RuleKey, Taclet> taclets = new LinkedHashMap<>();
    public List<Choice> seqChoices;
    public List<Object> contracts;
    public List<Object> invariants;
    public Term problemTerm;


    public Map<RuleKey, Taclet> getTaclets() {
        return taclets;
    }


    @Override
    public String toString() {
        return "ParsedKeyFile{" +
                "taclets=" + taclets +
                ", seqChoices=" + seqChoices +
                ", contracts=" + contracts +
                ", invariants=" + invariants +
                ", problemTerm=" + problemTerm +
                '}';
    }
}
