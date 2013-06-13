/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
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


    public ArrayList<Taclet> generateTaclets(Term post, Services services) {
        ArrayList<Term> postParts = extractPostParts(post, services);
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
            services.getProof().getIFSymbols().add(tacletBuilder.getTaclet());
            i++;
        }
        return removePostTaclets;
    }


    private ArrayList<Term> extractPostParts(Term post, Services services) {
        Function newIso =
                (Function)services.getNamespaces().functions().lookup("newObjectsIsomorphic");
        ArrayList<Term> postParts = new ArrayList<Term>();
        if (post.op() == Junctor.IMP) {
            postParts.add(post.sub(1));
        } else if (post.op() == Junctor.AND) {
            postParts.addAll(extractPostParts(post.sub(0), services));
            postParts.addAll(extractPostParts(post.sub(1), services));
        } else if (post.depth() == 1 || post.op() == Junctor.TRUE ||
                   post.op() == newIso || post.op() == Equality.EQUALS) {
            // do nothing
        } else {
            throw new IllegalArgumentException("error while extracting post " +
                                               "parts: information flow post " +
                                               "term malformed: " + post);
        }
        return postParts;
    }
}
