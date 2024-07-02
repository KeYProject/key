package de.uka.ilkd.key.api;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.MatchConditions;
import org.key_project.util.collection.ImmutableList;

/**
 * Created by sarah on 5/2/17.
 */
public class SearchNode {
    SequentFormula[] pattern;
    int pos = 0;
    int succAntPos = 0;
    public MatchConditions mc;
    ImmutableList<IfFormulaInstantiation> antec;
    ImmutableList<IfFormulaInstantiation> succ;



    public SearchNode(SequentFormula[] pattern, int succAntPos, ImmutableList<IfFormulaInstantiation> antec, ImmutableList<IfFormulaInstantiation> succ) {
        this.pattern = pattern;
        this.succAntPos = succAntPos;
        this.antec = antec;
        this.succ = succ;
        this.mc = MatchConditions.EMPTY_MATCHCONDITIONS;
    }

    public SearchNode(SearchNode parent, MatchConditions cond) {
        this.pattern = parent.pattern;
        this.succAntPos = parent.succAntPos;
        int parentPos = parent.pos;
        this.pos = parentPos+1;
        antec = parent.antec;
        succ = parent.succ;
        mc = cond;
    }

    public boolean isAntecedent() {
        return pos < succAntPos;
    }

    public Term getPatternTerm() {
        return pattern[pos].formula();
    }

    public boolean isFinished() {
        return pos >= pattern.length;
    }

}
