/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import java.util.ArrayList;


/**
 *
 * @author christoph
 */
public class SplitPostTacletBuilder {

    public static final Name SPLIT_POST_RULENAME = new Name("Split_post");


    public ArrayList<Taclet> generateTaclets(Term post) {
        ArrayList<Term> postParts = extractPostParts(post);
        ArrayList<Taclet> splitPostTaclets = new ArrayList<Taclet>();
        int i = 0;
        for (Term postPart : postParts) {
            ArrayList<Term> andTerms = extractAndTerms(postPart);

            RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
            tacletBuilder.setName(new Name(SPLIT_POST_RULENAME + "_" + i));
            tacletBuilder.setFind(postPart);
            tacletBuilder.setApplicationRestriction(RewriteTaclet.SUCCEDENT_POLARITY);
            tacletBuilder.setSurviveSmbExec(false);
            for (Term t : andTerms) {
                RewriteTacletGoalTemplate goal =
                        new RewriteTacletGoalTemplate(t);
                tacletBuilder.addTacletGoalTemplate(goal);
            }
            tacletBuilder.addRuleSet(new RuleSet(new Name("information_flow_contract_appl")));
            splitPostTaclets.add(tacletBuilder.getTaclet());
            i++;
        }
        return splitPostTaclets;
    }


    private ArrayList<Term> extractPostParts(Term post) {
        ArrayList<Term> postParts = new ArrayList<Term>();
        if (post.op() == Junctor.IMP) {
            postParts.add(post.sub(1));
        } else if (post.op() == Junctor.AND) {
            postParts.addAll(extractPostParts(post.sub(0)));
            postParts.addAll(extractPostParts(post.sub(1)));
        } else if (post.depth() == 1) {
            postParts.add(post); // TODO: Not sure about this
        } else {
            throw new IllegalArgumentException("error while extracting post " +
                                               "parts: information flowpost " +
                                               "term malformed: " + post);
        }
        return postParts;
    }


    private ArrayList<Term> extractAndTerms(Term term) {
        ArrayList<Term> andTerms = new ArrayList<Term>();
        if (term.op() == Junctor.AND) {
            andTerms.addAll(extractAndTerms(term.sub(0)));
            andTerms.addAll(extractAndTerms(term.sub(1)));
        } else {
            andTerms.add(term);
        }
        return andTerms;
    }
}
