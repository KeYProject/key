package de.uka.ilkd.key.speclang.jml.pretranslation;

import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

/**
 * A JML assert/assume statement.
 */
public class TextualJMLAssertStatement extends TextualJMLConstruct {

    private LabeledParserRuleContext context;
    private Kind kind;

    public TextualJMLAssertStatement(Kind kind, LabeledParserRuleContext clause) {
        super(ImmutableSLList.nil(), kind.toString() + " " + clause);
        this.kind = kind;
        this.context = clause;
    }

    public LabeledParserRuleContext getContext() {
        return context;
    }

    public String getClauseText() {
        return context.first.getText().substring(kind.toString().length());
    }

    public Kind getKind() {
        return kind;
    }

    public static enum Kind {
        ASSERT("assert"),
        ASSUME("assume");

        private String name;

        private Kind(String name) {
            this.name = name;
        }

        @Override
        public String toString() {
            return name;
        }
    };

}
