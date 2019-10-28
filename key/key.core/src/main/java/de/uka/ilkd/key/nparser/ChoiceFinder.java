package de.uka.ilkd.key.nparser;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (28.10.19)
 */
public class ChoiceFinder extends AbstractBuilder<Void> {
    private final Map<String, Set<String>> seq;

    public ChoiceFinder(Map<String, Set<String>> seq) {
        this.seq = seq;
    }

    public ChoiceFinder() {
        this(new HashMap<>());
    }

    @Override
    public Void visitDecls(KeYParser.DeclsContext ctx) {
        ctx.option_decls().forEach(this::accept);
        return null;
    }

    @Override
    public Void visitChoice(KeYParser.ChoiceContext ctx) {
        String category = ctx.category.getText();
        Set<String> options = new HashSet<>(ctx.choice_option.size());
        ctx.choice_option.forEach(it -> options.add(it.getText()));
        seq.put(category, options);
        return null;
    }

    public Map<String, Set<String>> getChoices() {
        return seq;
    }
}
