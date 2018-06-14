package org.key_project.jmlediting.profile.key.primary;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.UnarySpecExpressionArgParser;
import org.key_project.jmlediting.profile.jmlref.primary.AbstractJMLPrimaryKeyword;

public class StaticInvariantForKeyword extends AbstractJMLPrimaryKeyword {

    /**
     * Creates new instance for the static_invariant_for keyword.
     */
    public StaticInvariantForKeyword() {
       super("\\static_invariant_for");
    }

    @Override
    public String getDescription() {
       return "The \\static_invariant_for includes the static invariant of the enclosed type.";
    }

    @Override
    public IKeywordParser createParser() {
       return new UnarySpecExpressionArgParser();
    }
}
