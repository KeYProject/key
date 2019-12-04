package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (28.10.19)
 */
public class ChoiceFinder extends AbstractBuilder<Object> {
    private final Map<String, Set<String>> seq = new HashMap<>();
    private final HashSet<String> activatedChoicesCategories = new LinkedHashSet<>();
    private ImmutableSet<Choice> activatedChoices = DefaultImmutableSet.nil();
    private Namespace<Choice> choices = new Namespace<>();

    public ChoiceFinder() {
    }

    public ChoiceFinder(Namespace<Choice> choices) {
        this.choices = choices;
    }

    @Override
    public Object visitDecls(KeYParser.DeclsContext ctx) {
        ctx.option_decls().forEach(this::accept);
        ctx.options_choice().forEach(this::accept);
        return null;
    }

    @Override
    public Object visitChoice(KeYParser.ChoiceContext ctx) {
        String category = ctx.category.getText();
        Set<String> options = new HashSet<>(ctx.choice_option.size());
        ctx.choice_option.forEach(it -> {
            options.add(it.getText());
            choices.add(new Choice(it.getText(), category));
        });
        seq.put(category, options);
        return null;
    }

    @Override
    public Choice visitActivated_choice(KeYParser.Activated_choiceContext ctx) {
        var cat = ctx.cat.getText();
        var ch = ctx.choice_.getText();
        if (activatedChoicesCategories.contains(cat)) {
            throw new IllegalArgumentException("You have already chosen a different option for " + cat);
        }
        activatedChoicesCategories.add(cat);
        var name = cat + ":" + ch;
        var c = (Choice) choices.lookup(new Name(name));
        if (c == null) {
            semanticError(ctx, "Choice %s not previously declared", name);
        } else {
            activatedChoices = activatedChoices.add(c);
        }
        return c;
    }


    public Map<String, Set<String>> getChoices() {
        return seq;
    }

    public ImmutableSet<Choice> getActivatedChoices() {
        return activatedChoices;
    }
}
