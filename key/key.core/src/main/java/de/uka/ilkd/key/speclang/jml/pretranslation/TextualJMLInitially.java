package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import org.key_project.util.collection.ImmutableList;

import java.util.Objects;


/**
 * A JML initially clause declaration in textual form.
 *
 * @author Daniel Bruns
 */
public final class TextualJMLInitially extends TextualJMLConstruct {

    private final JmlParser.Initially_clauseContext inv;


    public TextualJMLInitially(ImmutableList<String> mods, JmlParser.Initially_clauseContext inv) {
        super(mods);
        this.inv = Objects.requireNonNull(inv);
        setPosition(inv);
    }

    public LabeledParserRuleContext getInv() {
        return new LabeledParserRuleContext(inv,
                createTermLabel(OriginTermLabel.SpecType.INVARIANT, inv.start,
                        inv.entity_name() != null ? inv.entity_name().ident().getText() : null));
    }

    @Override
    public String toString() {
        return inv.getText();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLInitially)) {
            return false;
        }
        TextualJMLInitially ci = (TextualJMLInitially) o;
        return mods.equals(ci.mods) && inv.equals(ci.inv);
    }


    @Override
    public int hashCode() {
        return mods.hashCode() + inv.hashCode();
    }
}