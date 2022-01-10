package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.key_project.util.collection.ImmutableSLList;

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

    /**
     * Transforms a rule context to a text representation.
     * Does the same as `context.getText` but inserts a space between all children of RuleContexts.
     *
     * This assumes the following tree layout:
     * `RuleContext (-> RuleContext)* -> Some leaf`
     */
    private static String ruleContextToText(RuleContext context) {
        if (context.getChildCount() == 0) {
            return "";
        }

        StringBuilder builder = new StringBuilder();
        for (int i = 0; i < context.getChildCount(); i++) {
            if (i > 0) {
                builder.append(' ');
            }

            var child = context.getChild(i);
            if (child instanceof RuleContext) {
                builder.append(ruleContextToText((RuleContext) child));
            } else {
                builder.append(child.getText());
            }
        }

        return builder.toString();
    }

    public String getClauseText() {
        var text = ruleContextToText(context.first);
        return text.substring(kind.toString().length());
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
