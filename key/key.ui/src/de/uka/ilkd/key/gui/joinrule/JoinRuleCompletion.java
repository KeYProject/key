package de.uka.ilkd.key.gui.joinrule;

import org.key_project.util.collection.ImmutableList;
import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.join.JoinRule;
import de.uka.ilkd.key.rule.join.JoinRuleBuiltInRuleApp;
import de.uka.ilkd.key.util.Pair;

/**
 * This class completes the instantiation for a join rule application.
 * The user is queried for partner goals to choose. If in forced mode,
 * all potential partners are chosen (no query is shown to the user).
 * 
 * @author Dominic Scheurer
 */
public class JoinRuleCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal,
            boolean forced) {

        JoinRuleBuiltInRuleApp joinApp = (JoinRuleBuiltInRuleApp) app;
        JoinRule joinRule = joinApp.rule();
        PosInOccurrence pio = joinApp.posInOccurrence();
        
        ImmutableList<Pair<Goal,PosInOccurrence>> candidates =
                joinRule.findPotentialJoinPartners(goal, pio);
        
        ImmutableList<Pair<Goal,PosInOccurrence>> chosenCandidates = null;
        
        if (forced) {
            chosenCandidates = candidates;
        } else {
            JoinPartnerSelectionDialog dialog =
                    new JoinPartnerSelectionDialog(goal, pio, candidates, goal.proof().getServices());
            dialog.setVisible(true);
            chosenCandidates = dialog.getChosen();
        }
        
        JoinRuleBuiltInRuleApp result = new JoinRuleBuiltInRuleApp(joinApp.rule(), pio);
        result.setJoinPartners(chosenCandidates);
        
        return result;
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }
    
    public static boolean checkCanComplete(IBuiltInRuleApp app) {
        return app instanceof JoinRuleBuiltInRuleApp;
    }

}
