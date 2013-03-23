/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import java.util.ArrayList;


/**
 *
 * @author christoph
 */
public class RemovePostTacletBuilder {

    public static final Name REMOVE_POST_RULENAME = new Name("Remove_post");


    public ArrayList<Taclet> generateTaclets(Term post) {
        ArrayList<Term> postParts = extractPostParts(post);
        ArrayList<Taclet> removePostTaclets = new ArrayList<Taclet>();
        int i = 0;
        for (Term postPart : postParts) {
            RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
            tacletBuilder.setName(new Name(REMOVE_POST_RULENAME + "_" + i));
            tacletBuilder.setFind(postPart);
            tacletBuilder.setApplicationRestriction(RewriteTaclet.SUCCEDENT_POLARITY);
            tacletBuilder.setSurviveSmbExec(false);
            RewriteTacletGoalTemplate goal =
                    new RewriteTacletGoalTemplate(TermBuilder.DF.ff());
            tacletBuilder.addTacletGoalTemplate(goal);
            tacletBuilder.addRuleSet(new RuleSet(new Name("information_flow_contract_appl")));
            removePostTaclets.add(tacletBuilder.getTaclet());
            i++;
        }
        return removePostTaclets;
    }


    private ArrayList<Term> extractPostParts(Term post) {
        ArrayList<Term> postParts = new ArrayList<Term>();
        if (post.op() == Junctor.IMP) {
            postParts.add(post.sub(1));
        } else if (post.op() == Junctor.AND) {
            postParts.addAll(extractPostParts(post.sub(0)));
            postParts.addAll(extractPostParts(post.sub(1)));
        } else if (post.depth() == 1) {
            postParts.add(post);
        } else if (post.op() == Junctor.TRUE) {
            // do nothing
        } else {
            throw new IllegalArgumentException("error while extracting post " +
                                               "parts: information flowpost term malformed.");
        }
        return postParts;
    }
}
