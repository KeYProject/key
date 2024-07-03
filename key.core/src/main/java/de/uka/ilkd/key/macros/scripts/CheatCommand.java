package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.ChoiceExpr;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletApplPart;
import de.uka.ilkd.key.rule.TacletAttributes;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import java.util.Map;

public class CheatCommand extends NoArgumentCommand {
    private static final Taclet CHEAT_TACLET;

    static {
        TacletApplPart applPart = new TacletApplPart(Sequent.EMPTY_SEQUENT, ImmutableList.of(), ImmutableList.of(), ImmutableList.of(), ImmutableList.of());
        CHEAT_TACLET = new NoFindTaclet(new Name("CHEAT"), applPart, ImmutableList.of(), ImmutableList.of(), new TacletAttributes(),
            DefaultImmutableMap.nilMap(), ChoiceExpr.TRUE, ImmutableSet.empty());
    }

    @Override
    public String getName() {
        return "cheat";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Void args, EngineState state)
            throws ScriptException, InterruptedException {
        Taclet cheat = CHEAT_TACLET;
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cheat);
        state.getFirstOpenAutomaticGoal().apply(app);
    }
}
