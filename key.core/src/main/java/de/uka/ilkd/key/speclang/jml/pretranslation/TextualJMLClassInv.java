package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import org.key_project.util.collection.ImmutableList;

import java.util.Objects;


/**
 * A JML class invariant declaration in textual form.
 */
public final class TextualJMLClassInv extends TextualJMLConstruct {
    private final JmlParser.Class_invariantContext inv;

    public TextualJMLClassInv(ImmutableList<JMLModifier> mods,
            JmlParser.Class_invariantContext ctx) {
        super(mods, null);
        inv = Objects.requireNonNull(ctx);
    }

    public String getName() {
        if (name == null && inv.entity_name() != null) {
            name = inv.entity_name().ident().getText();
        }
        return name;
    }

    public LabeledParserRuleContext getInv() {
        return new LabeledParserRuleContext(inv, createTermLabel(
                OriginTermLabel.SpecType.INVARIANT,
                inv.start, getName()));
    }


    @Override
    public String toString() {
        return inv.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLClassInv)) {
            return false;
        }
        TextualJMLClassInv ci = (TextualJMLClassInv) o;
        return mods.equals(ci.mods) && inv.equals(ci.inv);
    }


    @Override
    public int hashCode() {
        return Objects.hash(mods, inv);
    }
}
